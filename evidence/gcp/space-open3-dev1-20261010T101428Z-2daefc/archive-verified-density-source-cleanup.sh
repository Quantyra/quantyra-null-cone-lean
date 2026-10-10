set -eu
if pgrep -x lean || pgrep -x lake; then exit 1; fi
python3 - <<'PY'
from pathlib import Path
import json,tarfile,hashlib,shutil
runs=['space-density3-dev1-20261010T093644Z-5882c8', 'space-density3-dev2-20261010T094540Z-a2a222', 'space-density3-dev3-20261010T095034Z-f4fcdf', 'space-density3-dev4-20261010T095808Z-10e2f9']
expected={'space-density3-dev1-20261010T093644Z-5882c8': '31243964a06dbdfbea3000e1c269c68db7e27a08b4071ae7678da5f10f0a7517', 'space-density3-dev2-20261010T094540Z-a2a222': 'fd9d1eaa4a72a6a76b55500f8e605454152721c70392e61ffdcd836c0caba282', 'space-density3-dev3-20261010T095034Z-f4fcdf': '34fbde18f57d4cec2ba7898b765bb6b24cb3edb5750ab81d2913f8acc240dac2', 'space-density3-dev4-20261010T095808Z-10e2f9': 'af601e613031592a09e952b9a0d708bb8579bd9da9e9901e317b3147bcb6d394'}
base=Path.home()/'quantyra-space-runs'
removals=[]; receipts=[]
for run in runs:
 root=base/run
 assert root.resolve()==root and '-dev' in run and 'acceptance' not in run
 assert (root/'exit-code').read_text().strip() in {'0','1'}
 m=json.loads((root/'capture-manifest.json').read_text()); assert m['run']==run
 archive=root/'inputs.tar.gz'
 assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected[run],run
 source=root/'source'; assert source.resolve()==source and source.is_dir()
 size=0
 with tarfile.open(archive) as t:
  assert set(t.getnames())==set(m['source'])
  for name,sha in m['source'].items():
   assert hashlib.sha256(t.extractfile(name).read()).hexdigest()==sha,name
   f=source/name
   assert f.resolve().is_relative_to(source) and not f.is_symlink() and f.is_file()
   b=f.read_bytes(); assert hashlib.sha256(b).hexdigest()==sha,name
   removals.append(f);size+=len(b)
 receipts.append(dict(run=run,verified_files=len(m['source']),removed_source_bytes=size,archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest()))
for f in removals:f.unlink()
for item in receipts:print(json.dumps(item))
print('Preserved all immutable archives, manifests, logs, receipts, shared dependencies and caches; removed only verified redundant extracted development source files.')
print('Disk:',shutil.disk_usage(base))
PY
