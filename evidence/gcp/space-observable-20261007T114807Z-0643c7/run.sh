#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-observable-20261007T114807Z-0643c7"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo '6373de8fd1cbb1451c47f39be1a4d03d2530f87e8e976f83c443ca5eec1c168e  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
cp -a "$HOME/quantyra-space-runs/space-interpolation-20261007T112652Z-43e687/source/.lake/build" source/.lake/build
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
lake build QuantyraNullCone.FiniteTV > "$task_root/logs/sampling.stdout.txt" 2> "$task_root/logs/sampling.stderr.txt"
echo EXIT=0
