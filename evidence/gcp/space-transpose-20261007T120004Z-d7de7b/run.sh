#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-transpose-20261007T120004Z-d7de7b"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo '5af6c29ffb7ae220f525eb3067e92b32ff5a2e723367df0e8d42bd7d7ceb5338  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
cp -a "$HOME/quantyra-space-runs/space-observable-20261007T114943Z-041e63/source/.lake/build" source/.lake/build
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
echo STAGE=interpolation-lean
lake build QuantyraNullCone.Transpose > "$task_root/logs/sampling.stdout.txt" 2> "$task_root/logs/sampling.stderr.txt"
echo EXIT=0
