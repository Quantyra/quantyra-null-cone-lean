#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-20261007T093129Z-retry1"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; printf "%s\n" "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
printf 'RUN=space-20261007T093129Z-retry1\n'
cd /tmp

echo 'b21b8126defca58741deb508aa0ba07e5db2dc864340727b6e7ede0b460c3f72  space-pinned-dependencies.tar.gz' | sha256sum -c -
echo '4dad74141c2c119ca1aa626656be83b8e14238afba97271fd7bf1eb3f081b319  lean-4.30.0-linux.tar.zst' | sha256sum -c -
echo '294ce47bd2432506baa476c6ea001c5486657279757566153854cadd98137133  space-mathlib-cache.tar' | sha256sum -c -
mkdir -p "$HOME/quantyra-space-tools"
if [ ! -x "$HOME/quantyra-space-tools/lean-4.30.0-linux/bin/lean" ]; then
  tar --zstd -xf lean-4.30.0-linux.tar.zst -C "$HOME/quantyra-space-tools"
fi
export PATH="$HOME/quantyra-space-tools/lean-4.30.0-linux/bin:$PATH"
export MATHLIB_NO_CACHE_ON_UPDATE=1
export MATHLIB_CACHE_DIR="$task_root/cache"
mkdir -p "$task_root/inputs" "$task_root/packages" "$MATHLIB_CACHE_DIR"
cp -a "$HOME/quantyra-space-runs/space-20261007T090025Z-58150c4e/inputs/." "$task_root/inputs/"
cp -a "$HOME/quantyra-space-runs/space-20261007T090025Z-58150c4e/packages/." "$task_root/packages/"
for pkg in "$task_root/packages"/*; do
 git -C "$pkg" config core.autocrlf false
 git -C "$pkg" config core.filemode false
 git -C "$pkg" checkout-index --all --force
 git -C "$pkg" diff --exit-code HEAD --
done
tar -xf space-mathlib-cache.tar -C "$MATHLIB_CACHE_DIR"
cp -a "$task_root/inputs/baseline" "$task_root/baseline"
cp -a "$task_root/inputs/candidate" "$task_root/candidate"
for phase in baseline candidate; do
  mkdir -p "$task_root/$phase/.lake"
  ln -s "$task_root/packages" "$task_root/$phase/.lake/packages"
done
for pkg in "$task_root/packages"/*; do git -C "$pkg" read-tree HEAD; done
lean --version | tee "$task_root/logs/lean-version.txt"
lake --version | tee "$task_root/logs/lake-version.txt"
python3 - "$task_root" <<'PY'
import hashlib,json,subprocess,sys
from pathlib import Path
r=Path(sys.argv[1]);m=json.loads((r/'inputs/capture-manifest.json').read_text())
for kind in ['baseline','candidate']:
    for name,expected in m[kind].items():
        assert hashlib.sha256((r/kind/name).read_bytes()).hexdigest()==expected,name
for p in m['dependencies']:
    actual=subprocess.check_output(['git','-C',str(r/'packages'/p['name']),'rev-parse','HEAD'],text=True).strip()
    assert actual==p['rev'],p['name']
print('PASS: immutable source and exact dependency identities')
PY
cd "$task_root/baseline"
lake exe cache unpack > "$task_root/logs/cache.stdout.txt" 2> "$task_root/logs/cache.stderr.txt"
for phase in baseline candidate; do
  cd "$task_root/$phase"
  printf 'STAGE=%s-build\n' "$phase"
  lake build QuantyraNullCone > "$task_root/logs/$phase-build.stdout.txt" 2> "$task_root/logs/$phase-build.stderr.txt"
  printf 'STAGE=%s-audit\n' "$phase"
  python3 checks/check_integrity.py > "$task_root/logs/$phase-audit.stdout.txt" 2> "$task_root/logs/$phase-audit.stderr.txt"
done
cd "$task_root/candidate"
python3 checks/check_grid_witnesses.py > "$task_root/logs/grid-witnesses.txt" 2>&1
python3 checks/check_small_realizers.py > "$task_root/logs/small-realizers.txt" 2>&1
python3 checks/check_grid_scale.py > "$task_root/logs/grid-scale.txt" 2>&1
python3 - "$task_root" <<'PY'
import hashlib,json,re,subprocess,sys
from pathlib import Path
r=Path(sys.argv[1]);m=json.loads((r/'inputs/capture-manifest.json').read_text())
warnings={}
for kind in ['baseline','candidate']:
    for name,expected in m[kind].items():
        assert hashlib.sha256((r/kind/name).read_bytes()).hexdigest()==expected,name
    text='\n'.join(f.read_text(errors='replace') for f in (r/'logs').glob(kind+'-*txt'))
    warnings[kind]=re.findall(r'QuantyraNullCone[^\n]*: warning:',text)
    assert not re.search(r'error:|unsolved goals|sorryAx',text),kind
assert warnings['baseline']==warnings['candidate']==[],warnings
receipt={'run':'space-20261007T093129Z-retry1','source_capture_run':m['run'],'compile_host':'GCP','exit':0,'source_verified':True,
         'dependency_identities_verified':True,'owned_warning_headers':warnings,
         'candidate_exports':16,'baseline_exports':12}
(r/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: baseline/candidate build, exact-source audits and warning gate')
PY
printf 'EXIT=0\n'
