import json,runpy,tarfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
c=runpy.run_path(str(HERE/'space-cloud.py'),run_name='failure_collection')
state=json.loads((HERE/'current-space-gcp.json').read_text())
run=state['run'];out=Path(state['evidence'])
assert run=='space-thinning-coverage-dev8-20261009T223151Z-c58346'
c['ssh']('set -eu\nif pgrep -x lean || pgrep -x lake; then exit 1; fi\ncd "$HOME/quantyra-space-runs/'+run+'"\ntest -f exit-code\ntest ! -s exit-code\ntest ! -e logs/build.stdout.txt\ntar -czf /tmp/'+run+'-evidence.tar.gz logs exit-code started-utc launch.log\n','package-disk-failure')
archive=out/(run+'-evidence.tar.gz')
c['cloud'](['compute','scp',c['VM']+':/tmp/'+archive.name,str(archive),'--tunnel-through-iap'],'download-disk-failure')
with tarfile.open(archive,'r:gz') as t:
    for member in t.getmembers():
        if not member.isfile():continue
        dest=(out/member.name).resolve()
        assert dest.is_relative_to(out.resolve())
        dest.parent.mkdir(parents=True,exist_ok=True)
        dest.write_bytes(t.extractfile(member).read())
assert 'No space left on device' in (out/'logs/runner.stderr.txt').read_text()
(out/'disposition.json').write_text(json.dumps({'status':'infrastructure_failure_before_Lean',
'cache_copy_exhausted_remote_disk':True,'lean_build_started':False,'terminal_exit_code_unavailable':True,
'empty_exit_marker_preserved':True,'finished_timestamp_unavailable':True,'raw_evidence_collected':True},indent=2)+'\n')
print('RETAINED disk failure evidence',run)
