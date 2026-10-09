set -euo pipefail
if pgrep -x lean || pgrep -x lake; then echo active-Lean-work; exit 1; fi
python3 - <<'PY'
import json, pathlib, shutil
from datetime import datetime, timezone
base=(pathlib.Path.home()/'quantyra-space-runs').resolve()
runs=[
'space-thinning-subset-dev2-20261009T220219Z-2ea95d',
'space-thinning-selected-dev3-20261009T220731Z-04a767',
'space-thinning-coverage-dev4-20261009T221203Z-9f5a49',
'space-thinning-coverage-dev5-20261009T221543Z-1cbe39',
'space-thinning-coverage-dev6-20261009T222212Z-345073',
'space-thinning-coverage-dev7-20261009T222534Z-f83311']
targets=[]
for run in runs:
    root=base/run
    assert root.resolve()==root and root.parent==base
    assert (root/'exit-code').read_text().strip()=='1',run
    cache=root/'source/.lake/build'
    assert cache.resolve()==cache and cache.is_dir() and not cache.is_symlink(),cache
    assert cache.is_relative_to(root/'source/.lake'),cache
    targets.append(cache)
before=shutil.disk_usage(base)._asdict()
for cache in targets:
    shutil.rmtree(cache)
receipt={'utc':datetime.now(timezone.utc).isoformat(),
'no_other_lean_work':True,'removed_only_redundant_failed_task_build_caches':[str(p) for p in targets],
'all_terminal_exit_codes':1,'source_inputs_and_raw_logs_preserved':True,
'local_evidence_archives_previously_verified':True,
'disk_before':before,'disk_after':shutil.disk_usage(base)._asdict()}
print(json.dumps(receipt,indent=2))
PY
