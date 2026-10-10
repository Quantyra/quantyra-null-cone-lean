"""Verify an unpacked S048 source package; no Git, Lean, network or dependencies."""
import hashlib
import json
from pathlib import Path
import re
import tarfile

ROOT=Path(__file__).resolve().parents[2]
HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8'))

def verify(root=ROOT):
    manifest=read(root/'SOURCE-MANIFEST.json')
    for name,digest in manifest['files'].items():
        p=root/name
        assert p.resolve().is_relative_to(root.resolve()), name
        assert sha(p.read_bytes())==digest, ('package file',name)
    here=root/'manuscript/physical-volume'
    mapping=read(here/'formal-map.json')
    gcp=root/'evidence/gcp'/mapping['gcp_run']
    capture=read(gcp/'capture-manifest.json')
    assert sha((gcp/'inputs.tar.gz').read_bytes())==mapping['archive_sha256']
    with tarfile.open(gcp/'inputs.tar.gz') as archive:
        files={m.name:archive.extractfile(m).read() for m in archive.getmembers() if m.isfile()}
    assert set(files)==set(capture['source']) and len(files)==198
    assert all(sha(body)==capture['source'][name] for name,body in files.items())
    audit=(gcp/'logs/audit.stdout.txt').read_text(encoding='utf-8')
    axioms=dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",audit))
    axioms.update((n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",audit))
    assert len(axioms)==797
    for values in axioms.values():
        assert set(v.strip() for v in values.split(',') if v.strip())<={'propext','Classical.choice','Quot.sound'}
    for claim in mapping['claims']:
        for e in claim['exports']:
            assert e['accepted_type'] in audit and axioms[e['name']]==e['axioms']
            assert sha(files[e['source']])==e['source_sha256']
    receipt=read(gcp/'receipt.json')
    assert receipt['acceptance'] and receipt['exit']==receipt['owned_warnings']==0
    assert receipt['compile_host']=='GCP'
    review=read(here/'review.json')
    assert review['visual_review_complete'] and review['pages']==14
    assert review['pdf_sha256']==sha((here/'interval-volume-detection.pdf').read_bytes())
    assert review['tex_sha256']==sha((here/'interval-volume-detection.tex').read_bytes())
    assert review['formal_map_sha256']==sha((here/'formal-map.json').read_bytes())
    assert review['pages_reviewed']==list(range(1,15))
    literature=read(here/'literature-map.json')
    assert sha((here/literature['snapshot_file']).read_bytes())==literature['source_review_sha256']
    assert not literature['purchased_bytes_in_package']
    print(json.dumps({'status':'PASS','package_files':len(manifest['files']),
      'captured_sources':198,'accepted_axiom_reports':797,'reviewed_pdf_pages':14,
      'new_lean_invocations':0,'new_samples':0}))

if __name__=='__main__': verify()
