set -eu
if pgrep -x lean || pgrep -x lake; then exit 1; fi
python3 - <<'PY'
from pathlib import Path
import json,tarfile,hashlib,shutil
runs=['space-join3-dev3-20261010T061740Z-9a6e85', 'space-join3-dev2-20261010T061554Z-a7f4c8', 'space-join3-dev1-20261010T060917Z-1bb123', 'space-curve3-dev4-20261010T055029Z-cf63cf', 'space-curve3-dev5-20261010T055203Z-d33534', 'space-curve3-dev3-20261010T054850Z-e35b42', 'space-curve3-dev2-20261010T054653Z-6f68a2', 'space-curve3-dev1-20261010T054214Z-f9adf6', 'space-boundary-dev2-20261010T052500Z-88557a', 'space-boundary-dev1-20261010T051945Z-89541c', 'space-gaugelabel-dev1-20261010T045917Z-a3e0aa', 'space-volumerate-dev3-20261010T022414Z-3a4191', 'space-volumerate-dev2-20261010T021817Z-cd3a43', 'space-volumerate-dev1-20261010T021018Z-b30ba3', 'space-volumeupper-dev3-20261010T015315Z-bbd9b4', 'space-volumeupper-dev2-20261010T014759Z-786575', 'space-volumeupper-dev1-20261010T014014Z-b7048d', 'space-confounding-dev6-20261010T011627Z-2f4fb4', 'space-confounding-dev5-20261010T011240Z-e8f6d0', 'space-confounding-dev4-20261010T010920Z-87837c']
expected={'space-join3-dev3-20261010T061740Z-9a6e85': '2719528d599b607f5c3070dbc54ccaa6dee4d5d1734f6cb738ec2292be7fe86e', 'space-join3-dev2-20261010T061554Z-a7f4c8': 'dc9af583bf7f0238474b17ca14d263ca374b0095ea3ae06bad462a38e809e6a5', 'space-join3-dev1-20261010T060917Z-1bb123': '2a44c65d17ad4235f633975d12b3e3cd79bae33584210c8058d0b1ce562a4c4d', 'space-curve3-dev4-20261010T055029Z-cf63cf': '2b9bba1733a9f956baf2f23c9d8d69b89f9a08214e87874af8ea4fa071efe2d8', 'space-curve3-dev5-20261010T055203Z-d33534': '81fb18d75f9437a149d4e83accfe692da1a9db7b33ea172840fafe64ebaadc8b', 'space-curve3-dev3-20261010T054850Z-e35b42': '057968628a523a125251822ccc398418d7211cb739c7fef90c9048f5ad655140', 'space-curve3-dev2-20261010T054653Z-6f68a2': '7a85ce0626b75631329d0331446c79ad866b058f2ece8ebd8cdf372dc07d5629', 'space-curve3-dev1-20261010T054214Z-f9adf6': 'a545d38886c49051e9eddefa9ff44df294d256bfa6ed267df4b079958fa848ff', 'space-boundary-dev2-20261010T052500Z-88557a': 'eca9125eb9e8cc557cd8da66bb2fac04d38628c76147d5d05ef2c1bbab9d9df3', 'space-boundary-dev1-20261010T051945Z-89541c': 'da67288eec1e736ba9b55ad5e37981f28f761bd2fda247b19149c4caa2aaafd7', 'space-gaugelabel-dev1-20261010T045917Z-a3e0aa': '745f8fe31930c46a477e50a5a18aff5f502fafed227b618cce8a80c3090827db', 'space-volumerate-dev3-20261010T022414Z-3a4191': 'd2079473457f5a4a9aca38e04db3ab3c8ab123d7167e0c2a83fc20988625e3b9', 'space-volumerate-dev2-20261010T021817Z-cd3a43': 'be4841efd1e1313151c33d00eb5dc389d8ea86efe5c1d72d6172346ad83fcda3', 'space-volumerate-dev1-20261010T021018Z-b30ba3': 'ddb3063f5544a2c6c35c6a62fd852b0b60efb81f973540d0f3f82da2e9f3b56c', 'space-volumeupper-dev3-20261010T015315Z-bbd9b4': '60d4e12749d455e0724425b2185e7d6e09be9f5a82be8fc590e7a81065d94d30', 'space-volumeupper-dev2-20261010T014759Z-786575': 'd817b7ebc9ccc53195fba1294044fd0d29d45391bb10f760945362720eaa6eec', 'space-volumeupper-dev1-20261010T014014Z-b7048d': '3f7ffc3f87d073f6ca031af28a98cf5a39ab9a4c332502aad04c188b420562ef', 'space-confounding-dev6-20261010T011627Z-2f4fb4': '0d40a2c256fe4b24707d98346b5066085d1fd80910f5cbd78e3c2c58e36e0d0f', 'space-confounding-dev5-20261010T011240Z-e8f6d0': '0ecfdc6175539140b3c51fe5fb4d6426435d927e3e6bf70e39404ce939080bc8', 'space-confounding-dev4-20261010T010920Z-87837c': 'db577d3bd3f5dd74f87ede944cc8881198966d7dea0a187203c134a1daa6b245'}
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
