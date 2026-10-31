#!/bin/zsh
# 概要：worktree 共通の mkdir 鍵でビルドを直列化する。
# 方針：owner.json の PID を確認し、終了・中断時に自分の鍵だけを除く。
# 規約：--wait 0 は即時保留（終了 75）。既定無期限、再確認 10 秒。
# 使われ方：zsh scripts/refactor/with_build_lock.sh --wait 0 -- lake build Module
exec python3 - "$@" <<'PY'
import argparse
import contextlib
import datetime
import fcntl
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

p=argparse.ArgumentParser(description='Serialize builds across worktrees; busy timeout exits 75.')
p.add_argument('--wait',type=float,default=None)
p.add_argument('command',nargs=argparse.REMAINDER)
a=p.parse_args()
if a.command[:1]==['--']: a.command.pop(0)
if not a.command or (a.wait is not None and (a.wait<0 or not math.isfinite(a.wait))): p.error('command and non-negative --wait required')
base=Path(os.environ.get('TMPDIR') or '/tmp').resolve()
lock=base/'serre-lake-build.lock'
# Serialize owner publication/reaping as well as mkdir. The small guard file stays;
# kernel flock is released even on SIGKILL. It prevents deleting a replacement lock.
guard=base/'serre-lake-build.guard'
token=uuid.uuid4().hex
owner={'pid':os.getpid(),'worktree':str(Path.cwd().resolve()),'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':a.command,'token':token}
child=None; acquired=False; interrupted=0

def handle(signum,_frame):
    global interrupted
    interrupted=signum
    if child is not None:
        try: os.killpg(child.pid,signum)
        except ProcessLookupError: pass

for sig in (signal.SIGINT,signal.SIGTERM,signal.SIGHUP): signal.signal(sig,handle)

@contextlib.contextmanager
def protected():
    with guard.open('a') as stream:
        fcntl.flock(stream,fcntl.LOCK_EX)
        yield

def read_owner():
    try:
        value=json.loads((lock/'owner.json').read_text())
        return value if isinstance(value,dict) else None
    except (OSError,ValueError): return None

def alive(pid):
    if not isinstance(pid,int) or pid<=0: return True
    try: os.kill(pid,0);return True
    except ProcessLookupError: return False
    except PermissionError: return True

def erase():
    # Never recursively delete unexpected contents or follow a symlink.
    (lock/'owner.json').unlink(missing_ok=True)
    lock.rmdir()

try:
    ps=subprocess.run(['ps','-axo','command='],capture_output=True,text=True)
    if ps.returncode: print('warning: cannot inspect unguarded lake builds: '+ps.stderr.strip(),file=sys.stderr)
    else:
        lines=[l for l in ps.stdout.splitlines() if __import__('re').search(r'(?:^|[/\s])lake\s+build(?:\s|$)',l) and 'with_build_lock.sh' not in l]
        if lines: print('warning: existing lake build (possibly unguarded):\n'+'\n'.join(lines),file=sys.stderr)
    started=time.monotonic(); last_notice=-float('inf')
    while not acquired:
        if interrupted: sys.exit(128+interrupted)
        with protected():
            if lock.is_symlink(): raise RuntimeError('refuse symlink lock directory')
            if lock.exists():
                previous=read_owner()
                if previous and not alive(previous.get('pid')):
                    erase()
                elif previous is None and time.time()-lock.stat().st_mtime>60:
                    # A crash between mkdir and publication leaves no live owner.
                    # Only reclaim an empty/incomplete directory after a grace period.
                    erase()
            try:
                lock.mkdir()
                try: (lock/'owner.json').write_text(json.dumps(owner,ensure_ascii=False)+'\n')
                except BaseException:
                    erase();raise
                acquired=True
            except FileExistsError: previous=read_owner()
        if acquired: break
        now=time.monotonic()
        if now-last_notice>=60:
            print('waiting for build lock: '+json.dumps(previous,ensure_ascii=False),file=sys.stderr,flush=True);last_notice=now
        if a.wait is not None and now-started>=a.wait: sys.exit(75)
        delay=10 if a.wait is None else min(10,max(0,a.wait-(now-started)))
        # Short sleep slices let signal cleanup run promptly.
        until=time.monotonic()+delay
        while time.monotonic()<until and not interrupted: time.sleep(min(.1,until-time.monotonic()))
    if interrupted: sys.exit(128+interrupted)
    child=subprocess.Popen(a.command,start_new_session=True)
    if interrupted: handle(interrupted,None)
    rc=child.wait()
    sys.exit(128+interrupted if interrupted else (128-rc if rc<0 else rc))
except (OSError,RuntimeError) as exc:
    print('with_build_lock: '+str(exc),file=sys.stderr);sys.exit(1)
finally:
    if acquired:
        with protected():
            current=read_owner()
            if current and current.get('token')==token: erase()
PY
