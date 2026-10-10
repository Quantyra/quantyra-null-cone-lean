"""Verify retained GCP evidence for a seeded, unchanged and edited cache probe.

This is an artifact audit, not a Lean invocation or theorem acceptance audit.
"""
from datetime import datetime
from pathlib import Path
import argparse
import hashlib
import json
import re
import tarfile


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def inspect_run(path):
    assert (path/'exit-code').read_text().strip() == '0'
    manifest = read_json(path/'capture-manifest.json')
    receipt = read_json(path/'receipt.json')
    assert receipt['compile_host'] == 'GCP' and receipt['exit'] == 0
    assert receipt['source_verified_before_and_after']
    archive = path/'inputs.tar.gz'
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == read_json(path/'input-archive.json')['sha256']
    with tarfile.open(archive) as bundle:
        assert set(bundle.getnames()) == set(manifest['source'])
        for name, expected in manifest['source'].items():
            assert hashlib.sha256(bundle.extractfile(name).read()).hexdigest() == expected, name
    stdout = (path/'logs/build.stdout.txt').read_text(encoding='utf-8')
    stderr = (path/'logs/build.stderr.txt').read_text(encoding='utf-8')
    assert not re.search(r'warning:|error:|unsolved goals|sorryAx', stdout+'\n'+stderr)
    before = read_json(path/'cache-before.json')['artifacts']
    after = read_json(path/'cache-after.json')['artifacts']
    first = datetime.fromisoformat((path/'build-started-utc').read_text().strip().replace('Z','+00:00'))
    last = datetime.fromisoformat((path/'build-finished-utc').read_text().strip().replace('Z','+00:00'))
    return {'manifest':manifest, 'before':before, 'after':after,
            'build_seconds':(last-first).total_seconds(), 'stdout':stdout,
            'checkpoint':read_json(path/'cache-checkpoint.json')}


def verify(seed_path, replay_path, edit_path):
    seed, replay, edit = map(inspect_run, (seed_path,replay_path,edit_path))
    probe = 'QuantyraNullCone/CampaignCacheProbe.lean'
    dependent = 'QuantyraNullCone/CampaignCacheDependent.lean'
    for run in (replay,edit):
        assert run['manifest']['dependencies'] == seed['manifest']['dependencies']
        assert run['manifest']['campaign'] == seed['manifest']['campaign']
        assert run['manifest']['source']['lean-toolchain'] == seed['manifest']['source']['lean-toolchain']
        assert run['manifest']['source']['lake-manifest.json'] == seed['manifest']['source']['lake-manifest.json']
    assert read_json(replay_path/'cache-restored-from.json') == seed['checkpoint']
    assert read_json(edit_path/'cache-restored-from.json') == replay['checkpoint']
    for previous, successor in ((seed,replay),(replay,edit)):
        assert {n:v['sha256'] for n,v in previous['after'].items()} == {
            n:v['sha256'] for n,v in successor['before'].items()}
    assert replay['before'] == replay['after']
    assert not re.search(r'\] Built QuantyraNullCone\.',replay['stdout'])
    assert replay['manifest']['source'][probe] == seed['manifest']['source'][probe]
    assert edit['manifest']['source'][probe] != replay['manifest']['source'][probe]
    assert edit['manifest']['source'][dependent] == replay['manifest']['source'][dependent]
    # Additional authored sources may have been captured between probes; none
    # belongs to the probe import closure, and none is built during the test.
    common = set(seed['manifest']['source']) & set(replay['manifest']['source']) & set(edit['manifest']['source'])
    assert all(seed['manifest']['source'][n] == replay['manifest']['source'][n]
               == edit['manifest']['source'][n] for n in common-{probe})
    expected_modules = {'QuantyraNullCone.CampaignCacheProbe','QuantyraNullCone.CampaignCacheDependent'}
    built = set(re.findall(r'\] Built (QuantyraNullCone\.[A-Za-z0-9_]+)',edit['stdout']))
    assert built == expected_modules, built
    assert edit['before'].keys() == edit['after'].keys()
    changed = {n for n in edit['before'] if edit['before'][n] != edit['after'][n]}
    expected_changed = {'lib/lean/'+name.replace('.','/')+suffix
                        for name in expected_modules for suffix in ('.olean','.ilean','.trace')}
    assert changed == expected_changed, changed
    for name in expected_modules:
        key = 'lib/lean/'+name.replace('.','/')+'.olean'
        assert edit['before'][key]['sha256'] != edit['after'][key]['sha256']
        assert edit['before'][key]['mtime_ns'] < edit['after'][key]['mtime_ns']
    return {
        'status':'PASS_GCP_INCREMENTAL_CACHE_PROBE',
        'campaign':seed['manifest']['campaign'],
        'runs':[path.name for path in (seed_path,replay_path,edit_path)],
        'seed_build_seconds':seed['build_seconds'],
        'unchanged_build_seconds':replay['build_seconds'],
        'edited_build_seconds':edit['build_seconds'],
        'tracked_artifacts_unchanged_on_replay':len(replay['after']),
        'edited_rebuilt_modules':sorted(built),
        'edited_changed_tracked_artifacts':sorted(changed),
        'scope':'Actual GCP build duration, excluding transport, cache compression/extraction and artifact collection; no whole-theorem certification or general runtime guarantee.',
        'cache_policy':'Persistent compressed task-owned checkpoint, exact archive/toolchain/dependency verification, fresh RAM extraction each run. Prior RAM-only reuse failed and its evidence remains preserved.',
        'formal_certification':False,
        'local_lean_invocations':0,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('seed',type=Path)
    parser.add_argument('replay',type=Path)
    parser.add_argument('edit',type=Path)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    result = verify(args.seed,args.replay,args.edit)
    result['verifier_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    rendered = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(rendered,encoding='utf-8')
    print(rendered,end='')
