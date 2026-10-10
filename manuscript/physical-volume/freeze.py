"""Create once (--write) or verify the unpublished v0.1.0 manuscript package."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
DEST=HERE/'prepared/v0.1.0'
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
PDF='interval-volume-detection.pdf'
ZIP='interval-volume-detection-source.zip'
TOP=['CLAIMS.md','README.md','prepare.py','build.py','freeze.py','verify_bundle.py',
     'interval-volume-detection.tex',PDF,'interval-volume-detection.log','tex-build.log',
     'formal-map.json','literature-map.json','source-review.snapshot.txt','evidence-manifest.json',
     'pilot-widths.tex','finite-widths.tex','table-data.json','review.json']

def payload():
    subprocess.run([sys.executable,str(HERE/'prepare.py')],cwd=ROOT,check=True)
    review=read(HERE/'review.json')
    assert review['visual_review_complete'] and review['pages_reviewed']==list(range(1,15))
    assert review['tex_sha256']==sha((HERE/'interval-volume-detection.tex').read_bytes())
    assert review['pdf_sha256']==sha((HERE/PDF).read_bytes())
    assert review['formal_map_sha256']==sha((HERE/'formal-map.json').read_bytes())
    files={}
    for name,digest in read(HERE/'evidence-manifest.json')['files'].items():
        body=(ROOT/name).read_bytes()
        assert sha(body)==digest, name
        files[name]=body
    for name in TOP:
        p=HERE/name
        files[p.relative_to(ROOT).as_posix()]=p.read_bytes()
    # No external article PDF is part of this explicitly enumerated payload.
    assert [n for n in files if n.endswith('.pdf')]==['manuscript/physical-volume/'+PDF]
    inner={'status':'unpublished preparation','version':'0.1.0',
           'files':{name:sha(body) for name,body in sorted(files.items())}}
    files['SOURCE-MANIFEST.json']=(json.dumps(inner,indent=2)+'\n').encode()
    buf=io.BytesIO()
    with zipfile.ZipFile(buf,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as archive:
        for name,body in sorted(files.items()):
            info=zipfile.ZipInfo(name,date_time=(2026,10,10,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED
            info.external_attr=0o100644<<16
            archive.writestr(info,body,compresslevel=9)
    return buf.getvalue(),len(inner['files'])

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    archive,count=payload()
    outputs={PDF:(HERE/PDF).read_bytes(),ZIP:archive}
    manifest={'status':'prepared, unpublished; no DOI or deposit','version':'0.1.0','pages':14,
      'proof_commit':'354fa1f8dc8746328077041ef79d3621837f99e7','source_package_files':count,
      'files':{n:{'sha256':sha(b),'bytes':len(b)} for n,b in outputs.items()}}
    outputs['manifest.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    if args.write: DEST.mkdir(parents=True,exist_ok=True)
    for name,body in outputs.items():
        p=DEST/name
        if args.write and not p.exists(): p.write_bytes(body)
        assert p.read_bytes()==body, ('frozen bytes differ; prepare a new revision',name)
    with zipfile.ZipFile(io.BytesIO(archive)) as package:
        inner=json.loads(package.read('SOURCE-MANIFEST.json'))
        assert set(package.namelist())==set(inner['files'])|{'SOURCE-MANIFEST.json'}
        assert package.testzip() is None
        for n,d in inner['files'].items(): assert sha(package.read(n))==d,n
    print(json.dumps({'status':'PASS','pages':14,'source_package_files':count,
      'zip_bytes':len(archive),'pdf_sha256':manifest['files'][PDF]['sha256'],
      'zip_sha256':manifest['files'][ZIP]['sha256'],'publication_performed':False}))

if __name__=='__main__': main()
