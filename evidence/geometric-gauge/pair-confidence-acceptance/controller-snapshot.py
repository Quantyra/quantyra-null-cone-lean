"""Isolated immutable GCP Lean development runs; no local Lean execution."""
import argparse,hashlib,io,json,runpy,subprocess,tarfile,uuid
from datetime import datetime,timezone
from pathlib import Path

HERE=Path(__file__).parent
SAT=Path(r'C:\Users\dfred\Desktop\Projects\IGH\quantyra-null-cone-lean')
parser=argparse.ArgumentParser()
parser.add_argument('mode',choices=['launch','submit','observe','collect','read'])
parser.add_argument('--label',default='degree-filter')
parser.add_argument('--target',default='QuantyraNullCone.DegreeFilter')
parser.add_argument('--script')
parser.add_argument('--accept',action='store_true')
parser.add_argument('--probe',type=int,choices=[1,2])
args=parser.parse_args()
if args.mode=='launch':
 run='space-'+args.label+'-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:6]
 out=SAT/'evidence/gcp'/run;out.mkdir(parents=True)
 names=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=SAT,text=True).splitlines()
 names=set(n for n in names if n.startswith(('QuantyraNullCone/','checks/')) or n in {'QuantyraNullCone.lean','lakefile.toml','lake-manifest.json','lean-toolchain','.github/workflows/verify.yml'})
 names.update(p.relative_to(SAT).as_posix() for p in (SAT/'QuantyraNullCone').glob('*.lean'))
 names.update(p.relative_to(SAT).as_posix() for p in (SAT/'checks').glob('*.py'))
 files={n:(SAT/n).read_bytes().replace(b'\r\n',b'\n') for n in sorted(names)}
 if args.probe:
  args.target='QuantyraNullCone.CampaignCacheDependent'
  files['QuantyraNullCone/CampaignCacheProbe.lean']=('import QuantyraNullCone.LorentzDensityForward\nnamespace QuantyraNullCone\ndef campaignCacheValue : Nat := '+str(args.probe)+'\ntheorem campaign_cache_value : campaignCacheValue = '+str(args.probe)+' := rfl\n#print axioms campaign_cache_value\nend QuantyraNullCone\n').encode()
  files['QuantyraNullCone/CampaignCacheDependent.lean']=b'import QuantyraNullCone.CampaignCacheProbe\nnamespace QuantyraNullCone\ntheorem campaign_cache_positive : 0 < campaignCacheValue := by norm_num [campaignCacheValue]\n#print axioms campaign_cache_positive\nend QuantyraNullCone\n'
 for n,b in files.items():
  text=b.decode('utf-8')
  assert not b.startswith(bytes([239,187,191])), 'BOM: '+n
  assert chr(65533) not in text, 'replacement character: '+n
  if n.endswith('.lean'):
   assert not __import__('re').search(r'^\s*(?:public\s+)?import\s+Mathlib(?:\.Tactic)?\s*$',text,__import__('re').MULTILINE), 'use focused imports: '+n
   for module in __import__('re').findall(r'^\s*(?:public\s+)?import\s+(Mathlib\.[A-Za-z0-9_.]+)',text,__import__('re').MULTILINE):
    assert (SAT/'.lake/packages/mathlib'/Path(module.replace('.','/')+'.lean')).is_file(), 'missing import '+module+' in '+n
   assert not __import__('re').search(r'\b(?:sorry|admit)\b|^\s*axiom\s',text,__import__('re').MULTILINE), 'unfinished declaration: '+n
 manifest={'run':run,'parent_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=SAT,text=True).strip(),
  'compile_host':'GCP','project':'quantyra-lean-cert-20260915','instance':'quantyra-lean-builder-01','zone':'us-central1-a',
  'campaign':'pair3-20261010T111516Z-a06b82','cache_policy':'task-owned incremental; per-run source and artifact inventories','probe':args.probe,'target':args.target,'source':{n:hashlib.sha256(b).hexdigest() for n,b in files.items()},'dependencies':json.loads(files['lake-manifest.json'])['packages']}
 (out/'capture-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
 with tarfile.open(out/'inputs.tar.gz','w:gz') as t:
  for n,b in files.items():
   info=tarfile.TarInfo(n);info.size=len(b);info.mode=0o644;t.addfile(info,io.BytesIO(b))
 sha=hashlib.sha256((out/'inputs.tar.gz').read_bytes()).hexdigest()
 (out/'input-archive.json').write_text(json.dumps({'sha256':sha})+'\n')
 script=r'''#!/usr/bin/env bash
set -euo pipefail
task_root="$HOME/quantyra-space-runs/RUN"
mkdir -p "$task_root/logs"
exec > >(tee "$task_root/logs/runner.stdout.txt") 2> >(tee "$task_root/logs/runner.stderr.txt" >&2)
trap 'code=$?; echo "$code" > "$task_root/exit-code"; date -u +%FT%TZ > "$task_root/finished-utc"' EXIT
date -u +%FT%TZ > "$task_root/started-utc"
cd "$task_root"
echo 'SHA  inputs.tar.gz' | sha256sum -c -
mkdir source
tar -xzf inputs.tar.gz -C source
mkdir -p source/.lake
ln -s "$HOME/quantyra-space-runs/space-20261007T093129Z-retry1/packages" source/.lake/packages
task_cache="/dev/shm/quantyra-space-RUN-build"
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
assert str(cache)=='/dev/shm/quantyra-space-RUN-build'
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
lake build TARGET > "$task_root/logs/build.stdout.txt" 2> "$task_root/logs/build.stderr.txt"
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
tar -I 'gzip -1' -cf "$task_store/cache-RUN-next.tar.gz" -C "$task_cache" .
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
'''.replace('RUN',run).replace('SHA',sha).replace('TARGET',args.target)
 if args.accept:
  script=script.replace('lake build '+args.target, 'lake build QuantyraNullCone')
  marker='python3 - "$task_root" <<\'PY\'\nimport hashlib,json,pathlib,sys'
  script=script.replace(marker, 'python3 checks/check_integrity.py > "$task_root/logs/audit.stdout.txt" 2> "$task_root/logs/audit.stderr.txt"\n'+marker)
  script=script.replace("(r/'receipt.json').write_text", "logs='\\n'.join(f.read_text() for f in (r/'logs').glob('*.txt'))\nassert not __import__('re').search('warning:|error:|unsolved goals|sorryAx',logs)\nexpected=(r/'source/checks/Audit.lean').read_text().count('#print axioms')\nassert (r/'logs/audit.stdout.txt').read_text().count(' depends on axioms:')+(r/'logs/audit.stdout.txt').read_text().count(' does not depend on any axioms')==expected\nfor p in m['dependencies']:\n d=r/'source/.lake/packages'/p['name']\n assert __import__('subprocess').check_output(['git','-C',str(d),'rev-parse','HEAD'],text=True).strip()==p['rev']\n __import__('subprocess').run(['git','-C',str(d),'diff','--exit-code','HEAD','--'],check=True,stdout=__import__('subprocess').DEVNULL)\n(r/'receipt.json').write_text")
  script=script.replace("'target':m['target'],'exit':0", "'target':'QuantyraNullCone','acceptance':True,'audited_exports':expected,'owned_warnings':0,'dependency_identities_before_and_after':True,'exit':0")
 (out/'run.sh').write_text(script,encoding='utf-8',newline='\n')
 (HERE/'current-space-gcp.json').write_text(json.dumps({'run':run,'evidence':str(out)}))
c=runpy.run_path(str(HERE/'space-cloud.py'),run_name='formal_control')
state=json.loads((HERE/'current-space-gcp.json').read_text());run=state['run'];out=Path(state['evidence'])
if args.mode in ['launch','submit']:
 status=c['cloud'](['compute','instances','describe',c['VM'],'--format=value(status)'],'instance-state').decode().strip()
 if not (out/'instance-ownership.json').exists():
  (out/'instance-ownership.json').write_text(json.dumps({'initial_state':status,'started_for_task':status=='TERMINATED'})+'\n')
 if status=='TERMINATED':c['cloud'](['compute','instances','start',c['VM']],'start-instance')
 elif status!='RUNNING':raise RuntimeError('Instance not ready: '+status)
 preflight='''if pgrep -x lean || pgrep -x lake; then exit 1; fi\necho no-other-Lean-work\npython3 -c "import shutil; d=shutil.disk_usage(chr(47)); print(d); assert d.free > 256*1024*1024; r=shutil.disk_usage(chr(47)+'dev'+chr(47)+'shm'); print(r); assert r.free > 256*1024*1024; m=open(chr(47)+'proc'+chr(47)+'meminfo').read(); a=int(m.split('MemAvailable:')[1].split()[0]); print('MemAvailable_KiB',a); assert a > 4*1024*1024"\n'''
 for attempt in range(3):
  stage='preflight-'+datetime.now(timezone.utc).strftime('%H%M%S')
  try:
   c['ssh'](preflight,stage)
   break
  except RuntimeError:
   code=json.loads((out/(stage+'.exit.json')).read_text())['exit']
   transport = code in [255,3221225477] or (code == 1 and 'Remote side unexpectedly closed network connection' in (out/(stage+'.stderr.txt')).read_text(encoding='utf-8',errors='replace'))
   if not transport or attempt==2:raise
   __import__('time').sleep(15)
 c['scp']([out/'inputs.tar.gz',out/'capture-manifest.json',out/'run.sh'],'upload-inputs')
 c['ssh']('set -e\ntask_root="$HOME/quantyra-space-runs/'+run+'"\ntest ! -e "$task_root"\nmkdir -p "$task_root"\ncp /tmp/inputs.tar.gz /tmp/capture-manifest.json /tmp/run.sh "$task_root/"\nset +e\nbash "$task_root/run.sh" > "$task_root/launch.log" 2>&1 < /dev/null\ntask_exit=$?\nset -e\ngrep -A 18 -E "^(error:|warning:)" "$task_root/logs/build.stdout.txt" || true\ntail -n 35 "$task_root/logs/build.stdout.txt"\nprintf "REMOTE_TERMINAL_EXIT=%s\\n" "$task_exit"\nexit "$task_exit"\n','launch')
 print('RUN',run,flush=True)
elif args.mode=='observe':
 c['ssh']('task_root="$HOME/quantyra-space-runs/'+run+'"\nfor task_tick in $(seq 1 20); do test ! -f "$task_root/exit-code" || break; sleep 1; done\nif test -f "$task_root/exit-code"; then cat "$task_root/exit-code"; else pgrep -af "lean|lake|'+run+'" || true; fi\ntail -n 65 "$task_root/logs/build.stdout.txt" 2>/dev/null || true\ntail -n 30 "$task_root/logs/build.stderr.txt" 2>/dev/null || true\nif test -f "$task_root/exit-code"; then printf "TERMINAL_EXIT="; cat "$task_root/exit-code"; fi\n','observation-'+datetime.now(timezone.utc).strftime('%H%M%S'))
elif args.mode=='read':
 assert args.script
 c['ssh'](Path(args.script).read_text(encoding='utf-8'),'read-'+datetime.now(timezone.utc).strftime('%H%M%S'))
elif args.mode=='collect':
 c['ssh']('set -e\ncd "$HOME/quantyra-space-runs/'+run+'"\ntest -f exit-code\ntar -czf /tmp/'+run+'-evidence.tar.gz logs exit-code started-utc finished-utc launch.log cache-before.json cache-after.json build-started-utc build-finished-utc '+('receipt.json' if False else '$(test ! -e receipt.json || echo receipt.json)')+' $(test ! -e cache-restored-from.json || echo cache-restored-from.json) $(test ! -e cache-checkpoint.json || echo cache-checkpoint.json)\ntail -n 100 logs/build.stdout.txt\n','package-evidence-'+datetime.now(timezone.utc).strftime('%H%M%S'))
 archive=out/(run+'-evidence.tar.gz')
 c['cloud'](['compute','scp',c['VM']+':/tmp/'+archive.name,str(archive),'--tunnel-through-iap'],'download-evidence')
 with tarfile.open(archive,'r:gz') as t:
  for member in t.getmembers():
   if not member.isfile():continue
   dest=(out/member.name).resolve();assert dest.is_relative_to(out.resolve())
   dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(t.extractfile(member).read())
 print('RETAINED',run,flush=True)
