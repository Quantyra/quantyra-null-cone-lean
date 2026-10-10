#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/space-pair3-dev21-20261010T122913Z-8ce6c7"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo '15d2beca95be5fce0a0a18cc420f96c24a6df09a9e9f8a18f2229d15ac138da8  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
task_cache="/dev/shm/quantyra-space-space-pair3-dev21-20261010T122913Z-8ce6c7-build"
task_store="$HOME/quantyra-space-runs/pair3-20261010T111516Z-a06b82-cache"
mkdir -p "$task_store"
exec 9>"$task_store/lock"
flock -n 9
test ! -e "$task_cache"
if test -f "$task_store/cache.tar.gz"; then
  python3 - "$task_root" "$task_store" <<'PY'
import hashlib,json,pathlib,sys
r=pathlib.Path(sys.argv[1]);d=pathlib.Path(sys.argv[2])
assert not d.is_symlink() and d.name=='pair3-20261010T111516Z-a06b82-cache'
m=json.loads((r/'capture-manifest.json').read_text());c=json.loads((d/'state.json').read_text())
assert c['campaign']==m['campaign']=='pair3-20261010T111516Z-a06b82'
assert c['toolchain']==m['source']['lean-toolchain']
assert c['manifest']==m['source']['lake-manifest.json']
assert hashlib.sha256((d/'cache.tar.gz').read_bytes()).hexdigest()==c['sha256']
(r/'cache-restored-from.json').write_text(json.dumps(c,indent=2)+'\n')
print('RESTORING_TASK_CACHE',c['last_run'],c['sha256'])
PY
  mkdir "$task_cache"
  tar -xzf "$task_store/cache.tar.gz" -C "$task_cache"
else
  cp -a "$HOME/quantyra-space-runs/space-process-acceptance-20261009T234349Z-57dc8e/source/.lake/build" "$task_cache"
  echo SEEDED_TASK_OWNED_CACHE
fi
ln -s "$task_cache" source/.lake/build
cat > "$task_root/cache-inventory.py" <<'PY'
import hashlib,json,pathlib,sys
r=pathlib.Path(sys.argv[1]);cache=(r/'source/.lake/build').resolve()
assert str(cache)=='/dev/shm/quantyra-space-space-pair3-dev21-20261010T122913Z-8ce6c7-build'
result={}
for path in sorted((cache/'lib/lean/QuantyraNullCone').rglob('*')):
 if path.is_file() and path.suffix in {'.olean','.ilean','.trace'}:
  st=path.stat()
  result[path.relative_to(cache).as_posix()]={'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'bytes':st.st_size,'mtime_ns':st.st_mtime_ns}
(r/('cache-'+sys.argv[2]+'.json')).write_text(json.dumps({'cache':str(cache),'artifacts':result},indent=2)+'\n')
print('CACHE_INVENTORY',sys.argv[2],len(result))
PY
python3 "$task_root/cache-inventory.py" "$task_root" before
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
date -u +%FT%TZ > "$task_root/build-started-utc"
set +e
lake build QuantyraNullCone.LorentzPairConditioning > "$task_root/logs/build.stdout.txt" 2> "$task_root/logs/build.stderr.txt"
task_build_exit=$?
set -e
date -u +%FT%TZ > "$task_root/build-finished-utc"
python3 "$task_root/cache-inventory.py" "$task_root" after
test "$task_build_exit" = 0
python3 - "$task_root" <<'PY'
import hashlib,json,pathlib,sys
r=pathlib.Path(sys.argv[1]);m=json.loads((r/'capture-manifest.json').read_text())
for n,h in m['source'].items(): assert hashlib.sha256((r/'source'/n).read_bytes()).hexdigest()==h,n
(r/'receipt.json').write_text(json.dumps({'run':m['run'],'compile_host':'GCP','target':m['target'],'exit':0,'source_verified_before_and_after':True},indent=2)+'\n')
print('PASS development build and source preservation')
PY
tar -I 'gzip -1' -cf "$task_store/cache-space-pair3-dev21-20261010T122913Z-8ce6c7-next.tar.gz" -C "$task_cache" .
python3 - "$task_root" "$task_store" <<'PY'
import hashlib,json,os,pathlib,sys
r=pathlib.Path(sys.argv[1]);d=pathlib.Path(sys.argv[2]);m=json.loads((r/'capture-manifest.json').read_text())
assert not d.is_symlink() and d.name=='pair3-20261010T111516Z-a06b82-cache'
src=d/('cache-'+m['run']+'-next.tar.gz');dest=d/'cache.tar.gz'
assert src.is_file() and not src.is_symlink() and not dest.is_symlink()
state={'campaign':m['campaign'],'last_run':m['run'],'toolchain':m['source']['lean-toolchain'],
 'manifest':m['source']['lake-manifest.json'],'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'bytes':src.stat().st_size}
os.replace(src,dest)
(d/'state.json').write_text(json.dumps(state,indent=2)+'\n')
(r/'cache-checkpoint.json').write_text(json.dumps(state,indent=2)+'\n')
print('RETAINED_TASK_CACHE',state['sha256'],state['bytes'])
PY
