#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-identifiability-20261007T121032Z-4c3c47"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo '814688f4f5e6676af5e5c2adc8049416b98040362359d6025a8d1e3c5b440a2d  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
cp -a "$HOME/quantyra-space-runs/space-inverse-20261007T120449Z-c1319d/source/.lake/build" source/.lake/build
export PATH="$HOME/quantyra-space-tools/lean-4.30.0-linux/bin:$PATH"
export MATHLIB_NO_CACHE_ON_UPDATE=1
lean --version
python3 - "$task_root" <<'PY'
import hashlib,json,pathlib,sys
r=pathlib.Path(sys.argv[1]);m=json.loads((r/'capture-manifest.json').read_text())
for n,sha in m['source'].items():assert hashlib.sha256((r/'source'/n).read_bytes()).hexdigest()==sha,n
print('PASS exact source snapshot')
PY
for p in source/.lake/packages/*; do git -C "$p" diff --exit-code HEAD --; done
cd source
echo STAGE=observable-lean
lake build QuantyraNullCone > "$task_root/logs/sampling.stdout.txt" 2> "$task_root/logs/sampling.stderr.txt"
echo STAGE=integrity-audit
python3 checks/check_integrity.py > "$task_root/logs/audit.stdout.txt" 2> "$task_root/logs/audit.stderr.txt"
python3 - "$task_root" <<'PY'
import hashlib,json,pathlib,re,subprocess,sys
r=pathlib.Path(sys.argv[1]);m=json.loads((r/'capture-manifest.json').read_text())
for n,sha in m['source'].items():assert hashlib.sha256((r/'source'/n).read_bytes()).hexdigest()==sha,n
logs='\n'.join(f.read_text() for f in (r/'logs').glob('*.txt'))
assert not re.search('warning:|error:|unsolved goals|sorryAx',logs)
assert (r/'logs/audit.stdout.txt').read_text().count(' depends on axioms:')==55
for p in m['dependencies']:
 d=r/'source/.lake/packages'/p['name']
 assert subprocess.check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()==p['rev']
 subprocess.run(['git','-C',str(d),'diff','--exit-code','HEAD','--'],check=True,stdout=subprocess.DEVNULL)
(r/'receipt.json').write_text(json.dumps({'run':m['run'],'compile_host':'GCP','exit':0,'source_verified_before_and_after':True,'dependency_identities_and_clean_tracked_trees':True,'audited_exports':55,'owned_warnings':0},indent=2)+'\n')
print('PASS root build, 55 export audits, exact source/dependencies and zero warnings')
PY
echo EXIT=0
