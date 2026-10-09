"""Prepare the S045 publication edition and deterministic source archive.

Only date/status/DOI text changes from the reviewed S036 manuscript.
Build/render and actual visual review are separate; no Lean is invoked here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT/'manuscript/finite-data'
PACKAGE = PAPER/'deposit/v0.2.0'
BASE = PAPER/'revisions/v0.2.0'
REVIEWED = 'a9908d6115def3bec38ebae2ae1656cba54965d7'
PROOF = 'a0b1f6846d6f0b89a94704ed2954645bcac756fd'
STEM = 'finite-sample-order-density'


def sha(data): return hashlib.sha256(data).hexdigest()
def read(path): return json.loads(path.read_text(encoding='utf-8'))
def save(path, value): path.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8',newline='\n')


def publication_source(source, doi):
    replacements = [
        (r'\date{9 October 2026\\Version 0.2.0 --- unpublished working revision}',
         r'\date{9 October 2026\\Version 0.2.0\\\href{https://doi.org/'+doi+'}{'+doi+'}}'),
        ('artifacts and the frozen study are preserved. This is an unpublished\n'
         '0.2.0 working revision of the finite-data manuscript. Its published\n'
         '0.1.0 baseline remains at\n'
         r'\url{https://doi.org/10.5281/zenodo.23265067}; that DOI does not identify'+'\n'
         'this revised PDF. No publication of the revision is asserted here.',
         'artifacts and the frozen study are preserved. This is version 0.2.0\n'
         'of the finite-data manuscript, published in its existing Zenodo\n'
         'family with the DOI on the title page. The historical version\n'
         '0.1.0 remains available at\n'
         r'\url{https://doi.org/10.5281/zenodo.23265067}.'),
    ]
    for old,new in replacements:
        assert source.count(old)==1, 'Publication-label source mismatch'
        source=source.replace(old,new)
    return source


def prepare_source():
    assert not (PACKAGE/'published-record.json').exists(), 'Published payload is immutable'
    reservation=read(PACKAGE/'draft-record.json')
    assert reservation['conceptrecid']=='23265066' and reservation['previous_record']==23265067
    for name in (STEM+'.tex','formal-map.json','verification.md','verify_sources.py','source-verification.json','build.py'):
        original=subprocess.check_output(['git','show',f'{REVIEWED}:{(BASE/name).relative_to(ROOT).as_posix()}'],cwd=ROOT)
        assert original==(BASE/name).read_bytes(), ('Reviewed source changed',name)
        content=original.decode('utf-8')
        if name==STEM+'.tex':content=publication_source(content,reservation['doi'])
        if name=='build.py':
            content=content.replace('tmp/s036-manuscript-review','tmp/s045-manuscript-review')
            content=content.replace('manuscript/finite-data/revisions/v0.2.0/build.py','manuscript/finite-data/deposit/v0.2.0/build.py')
        (PACKAGE/name).write_text(content,encoding='utf-8',newline='\n')
    metadata=read(PAPER/'deposit/v0.1.0/zenodo-metadata.json')
    metadata['version']='0.2.0'
    metadata['related_identifiers'][0]['identifier']='https://github.com/Quantyra/quantyra-null-cone-lean/tree/'+PROOF
    metadata['keywords'] += ['minimax rate', 'randomized lower bound']
    metadata['description']=(
        '<p>We study full-square density estimation from one unlabeled strict directed causal order of n iid events. '
        'The original class consists of smooth densities on the unit square in [1/2,3/2], with exact uniform marginals '
        'and Euclidean Lipschitz constant at most two. Loss is supremum error modulo one global coordinate exchange.</p>'
        '<p>The accepted order-only estimator has 95% radius min{1/2,650(log n/n)^(1/4)} for every n at least 2. '
        'This revision adds a matching logarithmic lower bound: for n at least 2^64, every eligible estimator, '
        'including an arbitrary independent probability-space seed and with the stated success-event measurability, '
        'has strict error greater than (log n/n)^(1/4)/8192 with probability at least one half under some original-class density. '
        'Together these bounds establish the fixed-confidence minimax rate (log n/n)^(1/4) up to constants. '
        'The paper retains the two-point lower bound, actual-law corollary, complete degree-filter proof and band qualification, '
        'and adds the admissible many-density construction, testing proof, finite-scale calculation and minimax-radius argument.</p>'
        '<p>All main endpoints have exact-source Lean 4 acceptance on remote GCP. The manuscript maps 101 exports; '
        'the shared library audit contains 508 exact-type/axiom reports and a 3035-job root build, with zero warnings and standard axioms only. '
        'Earlier geometric forcing and the established second-moment testing method are attributed. Constants are conservative; '
        'the mathematical selector does not establish an efficient practical implementation, and the frozen uninformative pilot is preserved. '
        'The lower obstruction already holds with coordinate data. No additional order-information penalty, sharp constant, '
        'curvature recovery, physical validation or mathematical-priority claim is made.</p>'
        '<p>Author: Daniel Eric Fredriksen, Quantyra Inc. Developed with OpenAI Codex assistance. '
        'Review is open-source, decentralized and informal, through inspectable proofs and downstream testing. '
        'Manuscript materials are CC-BY-4.0; proof software and repository helpers retain Apache-2.0 licensing. '
        'This is a new version in the existing finite-data manuscript family, distinct from the reconstruction and coordinate-gauge papers.</p>')
    save(PACKAGE/'zenodo-metadata.json',metadata)
    (PACKAGE/'README.md').write_text(
        '# Finite data manuscript publication edition 0.2.0\n\n'
        f'Frozen publication package for [{reservation["doi"]}](https://doi.org/{reservation["doi"]}), '
        'in the existing finite-data family 23265066. The publication receipt records the live release result.\n\n'
        f'[PDF]({STEM}.pdf), [source]({STEM}.tex), [formal map](formal-map.json), '
        '[review](review.json), [source verification](source-verification.json), [manifest](manifest.json).\n\n'
        'Only title date/status/DOI and the publication-status paragraph differ from the reviewed S036 revision. '
        'Mathematical statements, proofs, attribution and limitations are preserved. '
        f'Reviewed source: `{REVIEWED}`; accepted proof: `{PROOF}`. '
        'The previous 0.1.0 publication and the 0.2.0 working revision remain intact.\n\n'
        'Lean/Lake execution is GCP-only. Build this PDF with build.py and Tectonic; '
        'verify_sources.py checks retained evidence without compiling Lean. '
        'Manuscript: CC-BY-4.0. Repository helpers and proofs: Apache-2.0.\n',encoding='utf-8',newline='\n')
    print('Prepared publication-label-only TeX, metadata and verification/build helpers.')


def bundle():
    assert not (PACKAGE/'published-record.json').exists(), 'Published payload is immutable'
    # Match the publication package's LF Git attributes before hashing.
    # Preserve raw compiler logs byte-for-byte under their -text attribute.
    for path in PACKAGE.iterdir():
        if path.is_file() and path.suffix in {'.json','.md','.py','.tex'}:
            data=path.read_bytes()
            if b'\r\n' in data:path.write_bytes(data.replace(b'\r\n',b'\n'))
    reservation=read(PACKAGE/'draft-record.json')
    original=subprocess.check_output(['git','show',f'{REVIEWED}:{(BASE/(STEM+".tex")).relative_to(ROOT).as_posix()}'],cwd=ROOT).decode('utf-8')
    assert (PACKAGE/(STEM+'.tex')).read_text(encoding='utf-8')==publication_source(original,reservation['doi'])
    review=read(PACKAGE/'review.json')
    assert review['all_pages_visually_inspected']==list(range(1,review['pages']+1))
    for suffix in ('.pdf','.tex'):
        assert review['files'][STEM+suffix]==sha((PACKAGE/(STEM+suffix)).read_bytes())
    excluded={'manifest.json','bundle.json','published-record.json','public-record.json','resolution-check.json'}
    payload=[p for p in sorted(PACKAGE.iterdir()) if p.is_file() and p.suffix!='.zip' and p.name not in excluded]
    payload += [PAPER/name for name in ('publish_version.py','test_version_publication.py','prepare_optimal_rate_release.py')]
    payload += [ROOT/'checks/zenodo_credentials.py',ROOT/'LICENSE',ROOT/'LICENSES/CC-BY-4.0.txt']
    manifest={'title':read(PACKAGE/'zenodo-metadata.json')['title'],'version':'0.2.0','doi':reservation['doi'],
              'proof_commit':PROOF,'reviewed_draft_commit':REVIEWED,'mathematical_body_unchanged':True,
              'source_change_scope':'Title date/status/DOI and publication-status paragraph only',
              'metadata_sha256':sha((PACKAGE/'zenodo-metadata.json').read_bytes()),
              'files':{p.relative_to(ROOT).as_posix():{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in payload}}
    save(PACKAGE/'manifest.json',manifest)
    target=PACKAGE/(STEM+'-v0.2.0-source.zip')
    with zipfile.ZipFile(target,'w') as archive:
        for path in payload+[PACKAGE/'manifest.json']:
            entry=zipfile.ZipInfo(path.relative_to(ROOT).as_posix(),(2026,10,9,0,0,0))
            entry.compress_type=zipfile.ZIP_DEFLATED;entry.external_attr=0o100644 << 16
            archive.writestr(entry,path.read_bytes())
    with zipfile.ZipFile(target) as archive:
        assert archive.testzip() is None
        for name,info in manifest['files'].items():assert sha(archive.read(name))==info['sha256']
    save(PACKAGE/'bundle.json',{'file':target.name,'sha256':sha(target.read_bytes()),'bytes':target.stat().st_size,'members':len(payload)+1})
    print('PASS: unchanged mathematics, reviewed files and deterministic source archive.')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=['source','bundle'])
    args=parser.parse_args()
    prepare_source() if args.mode=='source' else bundle()
