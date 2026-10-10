"""Windows single-process job supervision for the bounded S031 experiment.

Children are prohibited (ActiveProcessLimit=1), so the root working-set peak
is the complete allowed process-tree RSS. A job also caps total committed
memory; that distinct metric is reported separately. No credentials used.
"""
import ctypes as C
from ctypes import wintypes as W
import json
import os
from pathlib import Path
import subprocess
import sys
import time


class Basic(C.Structure):
    _fields_ = [('process_time', C.c_longlong), ('job_time', C.c_longlong),
                ('flags', W.DWORD), ('min_ws', C.c_size_t), ('max_ws', C.c_size_t),
                ('active_limit', W.DWORD), ('affinity', C.c_size_t),
                ('priority', W.DWORD), ('scheduling', W.DWORD)]


class IO(C.Structure):
    _fields_ = [(name, C.c_ulonglong) for name in
                ('read_ops', 'write_ops', 'other_ops', 'read_bytes', 'write_bytes', 'other_bytes')]


class Extended(C.Structure):
    _fields_ = [('basic', Basic), ('io', IO), ('process_memory', C.c_size_t),
                ('job_memory', C.c_size_t), ('peak_process_commit', C.c_size_t),
                ('peak_job_commit', C.c_size_t)]


class Memory(C.Structure):
    _fields_ = [('cb', W.DWORD), ('faults', W.DWORD)] + [
        (name, C.c_size_t) for name in ('peak_ws', 'ws', 'peak_paged', 'paged',
                                      'peak_nonpaged', 'nonpaged', 'pagefile', 'peak_pagefile')]


def supervise(code, args, log_path, seconds=600, rss_limit=4*1024**3,
              commit_limit=None, poll_seconds=.01):
    if os.name != 'nt':
        raise RuntimeError('this bounded runner requires Windows Job Objects')
    kernel, psapi = C.WinDLL('kernel32', use_last_error=True), C.WinDLL('psapi', use_last_error=True)
    kernel.CreateJobObjectW.argtypes, kernel.CreateJobObjectW.restype = [C.c_void_p, W.LPCWSTR], W.HANDLE
    kernel.SetInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD]
    kernel.QueryInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p]
    kernel.AssignProcessToJobObject.argtypes = [W.HANDLE, W.HANDLE]
    kernel.TerminateJobObject.argtypes = [W.HANDLE, W.UINT]
    kernel.CloseHandle.argtypes = [W.HANDLE]
    psapi.GetProcessMemoryInfo.argtypes = [W.HANDLE, C.c_void_p, W.DWORD]
    job = kernel.CreateJobObjectW(None, None)
    if not job:
        raise C.WinError(C.get_last_error())
    limits = Extended()
    limits.basic.flags = 0x2000 | 0x200 | 0x8  # kill, commit, active processes
    limits.basic.active_limit = 1
    limits.job_memory = commit_limit or rss_limit
    process = None
    started = time.perf_counter()
    peak = 0
    reason = 'completed'
    info = Extended()
    path = Path(log_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        if not kernel.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)):
            raise C.WinError(C.get_last_error())
        with path.open('xb') as log:
            # No numerical imports/work until the supervisor attaches the job.
            bootstrap = 'import sys; assert sys.stdin.buffer.read(1)==b"G"; '+code
            env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1', MKL_NUM_THREADS='1')
            process = subprocess.Popen([sys.executable, '-c', bootstrap, *map(str, args)],
                stdin=subprocess.PIPE, stdout=log, stderr=subprocess.STDOUT,
                creationflags=subprocess.CREATE_NO_WINDOW, env=env)
            if not kernel.AssignProcessToJobObject(job, int(process._handle)):
                raise C.WinError(C.get_last_error())
            process.stdin.write(b'G')
            process.stdin.close()
            while process.poll() is None:
                mem = Memory()
                mem.cb = C.sizeof(mem)
                if psapi.GetProcessMemoryInfo(int(process._handle), C.byref(mem), C.sizeof(mem)):
                    peak = max(peak, mem.peak_ws)
                else:
                    raise C.WinError(C.get_last_error())
                if peak > rss_limit:
                    reason = 'rss_limit'
                elif time.perf_counter()-started >= seconds:
                    reason = 'timeout'
                if reason != 'completed':
                    kernel.TerminateJobObject(job, 125)
                    break
                time.sleep(poll_seconds)
            process.wait(timeout=10)
            mem = Memory()
            mem.cb = C.sizeof(mem)
            if psapi.GetProcessMemoryInfo(int(process._handle), C.byref(mem), C.sizeof(mem)):
                peak = max(peak, mem.peak_ws)
            if not kernel.QueryInformationJobObject(job, 9, C.byref(info), C.sizeof(info), None):
                raise C.WinError(C.get_last_error())
        if reason == 'completed' and process.returncode:
            reason = 'worker_failed'
        if peak > rss_limit:
            reason = 'rss_limit'
        return {'outcome': reason, 'exit_code': process.returncode,
                'wall_seconds': time.perf_counter()-started,
                'process_tree_peak_rss_bytes': peak,
                'peak_job_committed_bytes': info.peak_job_commit,
                'rss_limit_bytes': rss_limit, 'committed_limit_bytes': limits.job_memory,
                'wall_limit_seconds': seconds, 'active_process_limit': 1,
                'poll_seconds': poll_seconds, 'log': path.name}
    finally:
        if process is not None and process.poll() is None:
            process.kill()
            process.wait()
        kernel.CloseHandle(job)


def probe(destination):
    dest = Path(destination)
    dest.mkdir(parents=True, exist_ok=True)
    timeout = supervise('import time; time.sleep(10)', [], dest/'timeout.log', seconds=.25)
    # Low committed-memory ceiling tests allocation rejection without 4-GiB stress.
    memory = supervise('a=bytearray(256*1024**2); print(len(a))', [], dest/'memory.log',
                       rss_limit=128*1024**2, commit_limit=64*1024**2)
    rss = supervise('import time; a=bytearray(64*1024**2); time.sleep(5)', [], dest/'rss.log',
                    rss_limit=32*1024**2, commit_limit=256*1024**2)
    child = supervise('exec("import subprocess\\ntry:\\n p=subprocess.run([sys.executable,\'-c\',\'print(123)\'])'
                      '\\n assert p.returncode != 0\\nexcept OSError:\\n pass\\nprint(\'child denied\')")',
                      [], dest/'child.log')
    ok = (timeout['outcome'] == 'timeout' and memory['exit_code'] != 0 and
          b'MemoryError' in (dest/'memory.log').read_bytes() and
          rss['outcome'] == 'rss_limit' and child['outcome'] == 'completed' and
          b'child denied' in (dest/'child.log').read_bytes())
    result = {'passed': ok, 'timeout': timeout, 'memory': memory, 'rss': rss, 'children': child,
              'scope': 'job commit/process limits plus 10-ms peak-RSS rejection watchdog; '
                       'root lifetime peak covers allowed tree because children are prohibited; '
                       'RSS overshoot is rejected, not represented as a hard instantaneous cap'}
    (dest/'probe.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    if not ok:
        raise RuntimeError('resource preflight failed; inspect retained logs')
    return result
