#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-volumeupper-dev1-20261010T014014Z-b7048d"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo '3f7ffc3f87d073f6ca031af28a98cf5a39ab9a4c332502aad04c188b420562ef  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
task_cache="/dev/shm/quantyra-space-space-volumeupper-dev1-20261010T014014Z-b7048d-build"
test ! -e "$task_cache"
cp -a "$HOME/quantyra-space-runs/space-process-acceptance-20261009T234349Z-57dc8e/source/.lake/build" "$task_cache"
ln -s "$task_cache" source/.lake/build
export PATH="$HOME/quantyra-space-tools/lean-4.30.0-linux/bin:$PATH"
export MATHLIB_NO_CACHE_ON_UPDATE=1
lean --version
python3 - "$task_root" <<'PY'
import hashlib,json,pathlib,subprocess,sys
r=pathlib.Path(sys.argv[1]);m=json.loads((r/'capture-manifest.json').read_text())
for n,h in m['source'].items(): assert hashlib.sha256((r/'source'/n).read_bytes()).hexdigest()==h,n
for p in m['dependencies']:
 d=r/'source/.lake/packages'/p['name']
 assert subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()==p['rev']
 subprocess.run(['git','-C',str(d),'diff','--exit-code','HEAD','--'],check=True,stdout=subprocess.DEVNULL)
print('PASS input and pinned dependency identities')
PY
cd source
lake build QuantyraNullCone.VolumeRateUpper > "$task_root/logs/build.stdout.txt" 2> "$task_root/logs/build.stderr.txt"
python3 - "$task_root" <<'PY'
import hashlib,json,pathlib,sys
r=pathlib.Path(sys.argv[1]);m=json.loads((r/'capture-manifest.json').read_text())
for n,h in m['source'].items(): assert hashlib.sha256((r/'source'/n).read_bytes()).hexdigest()==h,n
(r/'receipt.json').write_text(json.dumps({'run':m['run'],'compile_host':'GCP','target':m['target'],'exit':0,'source_verified_before_and_after':True},indent=2)+'\n')
print('PASS development build and source preservation')
PY
