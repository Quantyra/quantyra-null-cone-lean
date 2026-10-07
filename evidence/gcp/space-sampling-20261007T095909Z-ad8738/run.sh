#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-sampling-20261007T095909Z-ad8738"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo '1e8354e330ad0890ed86af0c21434abada4f6d4e3c9d1616e062e1b264d479d4  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
cp -a "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/candidate/.lake/build" source/.lake/build
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
echo STAGE=sampling-lean
lake env lean QuantyraNullCone/Sampling.lean > "$task_root/logs/sampling.stdout.txt" 2> "$task_root/logs/sampling.stderr.txt"
echo STAGE=probability-cache
export MATHLIB_CACHE_DIR="$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/cache"
lake exe cache get Mathlib.Probability.Moments.SubGaussian Mathlib.Probability.Independence.Basic > "$task_root/logs/cache.stdout.txt" 2> "$task_root/logs/cache.stderr.txt"
echo EXIT=0
