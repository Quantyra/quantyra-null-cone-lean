#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-firstretained-acceptance-20261010T003652Z-af3642"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo '9a3db8b3ca9e123bf03337d570722d64936c496cfe3cafd7226ae19b042d80b8  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
task_cache="/dev/shm/quantyra-space-space-firstretained-acceptance-20261010T003652Z-af3642-build"
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
lake build QuantyraNullCone > "$task_root/logs/build.stdout.txt" 2> "$task_root/logs/build.stderr.txt"
python3 checks/check_integrity.py > "$task_root/logs/audit.stdout.txt" 2> "$task_root/logs/audit.stderr.txt"
python3 - "$task_root" <<'PY'
import hashlib,json,pathlib,sys
r=pathlib.Path(sys.argv[1]);m=json.loads((r/'capture-manifest.json').read_text())
for n,h in m['source'].items(): assert hashlib.sha256((r/'source'/n).read_bytes()).hexdigest()==h,n
logs='\n'.join(f.read_text() for f in (r/'logs').glob('*.txt'))
assert not __import__('re').search('warning:|error:|unsolved goals|sorryAx',logs)
expected=(r/'source/checks/Audit.lean').read_text().count('#print axioms')
assert (r/'logs/audit.stdout.txt').read_text().count(' depends on axioms:')+(r/'logs/audit.stdout.txt').read_text().count(' does not depend on any axioms')==expected
for p in m['dependencies']:
 d=r/'source/.lake/packages'/p['name']
 assert __import__('subprocess').check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()==p['rev']
 __import__('subprocess').run(['git','-C',str(d),'diff','--exit-code','HEAD','--'],check=True,stdout=__import__('subprocess').DEVNULL)
(r/'receipt.json').write_text(json.dumps({'run':m['run'],'compile_host':'GCP','target':'QuantyraNullCone','acceptance':True,'audited_exports':expected,'owned_warnings':0,'dependency_identities_before_and_after':True,'exit':0,'source_verified_before_and_after':True},indent=2)+'\n')
print('PASS development build and source preservation')
PY
