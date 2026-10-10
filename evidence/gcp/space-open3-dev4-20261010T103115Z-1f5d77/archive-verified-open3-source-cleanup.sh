set -eu
if pgrep -x lean || pgrep -x lake; then exit 1; fi
python3 - <<'PY'
from pathlib import Path
import json,tarfile,hashlib,shutil
runs=['space-open3-dev1-20261010T101428Z-2daefc', 'space-open3-dev2-20261010T102116Z-6e109a', 'space-open3-dev3-20261010T102632Z-ce6bb1', 'space-open3-dev4-20261010T103115Z-1f5d77']
expected={'space-open3-dev1-20261010T101428Z-2daefc': '5ab72525a39e9dc7714749ee199357d6fc94124843da73432b3f85eca90982d6', 'space-open3-dev2-20261010T102116Z-6e109a': 'd338e212a9f920f43f8abd90db49b7b72f3bdea0cab19f151ad11fbaecd2f957', 'space-open3-dev3-20261010T102632Z-ce6bb1': '60062b862f274d4c8c840899a9376ebb41573260d8990d7bcc47782871d80b07', 'space-open3-dev4-20261010T103115Z-1f5d77': '158c566cc5746cfdf9a4e7b2a2ffaa07c7372d2d8cc370820a1a0440e78975a8'}
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
