#!/bin/zsh
# 概要：worktree 共通の mkdir 鍵でビルドを直列化する。待ち手は整理券で順に並ぶ。
# 方針：owner.json の PID を確認し、終了・中断時に自分の鍵と整理券だけを除く。
#       鍵が空いたとき、生きている整理券のうち順位が一番のものだけが取る。
#       順位は（組の順位、待ち始めた時刻）。組は impl・research・bulk の三つで、
#       昼（JST 8〜23 時）は impl → research → bulk、夜は bulk → impl → research。
#       繰り上げ：待ちが impl・research 15 分、bulk 30 分を超えた整理券は先頭の組へ（飢えの防止）。
#       ただし昼の bulk は繰り上げない（impl・research の整理券がないときだけ取る、11-11）。
# 規約：--wait 0 は即時保留（終了 75）。既定無期限、再確認 2 秒。
#       --class を省くと worktree 名から推定（main の作業木は coord、kerodon-layout は bulk、*-review は research、他は impl）。
#       coord（調整役の取り込み・登録）は昼夜とも常に先頭（11-11）。鍵の取得・返却は serre-lake-build.history.jsonl に追記。
#       --status は持ち主と待ちの列を表示して終了する。
#       夜（JST 23〜8 時）は鍵を二つ通す（11-11）。bulk は同時に一つまで。昼は一つ。
#       owner.json の started は鍵を取った時刻、queued は待ち始めた時刻（11-11 に分けた）。
# 使われ方：zsh scripts/refactor/with_build_lock.sh --wait 1800 -- lake build Module
exec python3 - "$@" <<'PY'
import argparse
import contextlib
import datetime
import fcntl
import json
import math
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import uuid

CLASSES=('coord','impl','research','bulk')
JST=datetime.timezone(datetime.timedelta(hours=9))

p=argparse.ArgumentParser(description='Serialize builds across worktrees with a fair ticket queue; busy timeout exits 75.')
p.add_argument('--wait',type=float,default=None)
p.add_argument('--class',dest='klass',choices=CLASSES,default=None)
p.add_argument('--status',action='store_true')
p.add_argument('command',nargs=argparse.REMAINDER)
a=p.parse_args()
if a.command[:1]==['--']: a.command.pop(0)
if not a.status and (not a.command or (a.wait is not None and (a.wait<0 or not math.isfinite(a.wait)))):
    p.error('command and non-negative --wait required')
base=Path(os.environ.get('TMPDIR') or '/tmp').resolve()
lock=base/'serre-lake-build.lock'
# Night (JST 23-8) admits two holders (11-11): slot 0 is the historical path, slot 1 is new.
# Old copies of this script only know slot 0, so they still serialize against slot 0.
SLOTS=[lock,base/'serre-lake-build.lock.1']
def jst_hour():
    # SERRE_LOCK_HOUR overrides the clock for tests only.
    h=os.environ.get('SERRE_LOCK_HOUR')
    return int(h) if h else datetime.datetime.now(JST).hour
def capacity(hour): return 1 if 8<=hour<23 else 2
queue=base/'serre-lake-build.queue'
# Serialize owner publication/reaping, ticket publication and the acquire decision.
# The small guard file stays; kernel flock is released even on SIGKILL.
guard=base/'serre-lake-build.guard'
# Append-only history of acquisitions and releases (11-11), for checking long holds afterwards.
history=base/'serre-lake-build.history.jsonl'
worktree=str(Path.cwd().resolve())

def infer_class(path):
    name=Path(path).name
    if name=='SerrePositivity': return 'coord'  # the main worktree: coordinator merges and registration
    if 'kerodon-layout' in name: return 'bulk'
    if name.endswith('-review') or '-review-' in name: return 'research'
    return 'impl'

klass=a.klass or infer_class(worktree)
token=uuid.uuid4().hex
enqueued=time.time()
queued_at=datetime.datetime.now(datetime.timezone.utc).isoformat()
# owner['started'] is the acquisition time (set when the lock is taken); 'queued' is when waiting began.
owner={'pid':os.getpid(),'worktree':worktree,'started':None,'queued':queued_at,
       'command':a.command,'token':token,'class':klass}
ticket=queue/f'{token}.json'
child=None; acquired=False; interrupted=0; ticketed=False; myslot=None

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

def read_json(path):
    try:
        value=json.loads(path.read_text())
        return value if isinstance(value,dict) else None
    except (OSError,ValueError): return None

def read_owner(slot=None): return read_json((slot or lock)/'owner.json')

def alive(pid):
    if not isinstance(pid,int) or pid<=0: return True
    try: os.kill(pid,0);return True
    except ProcessLookupError: return False
    except PermissionError: return True

def erase(slot=None):
    # Never recursively delete unexpected contents or follow a symlink.
    slot=slot or lock
    (slot/'owner.json').unlink(missing_ok=True)
    slot.rmdir()

def class_rank(c,hour):
    day=8<=hour<23
    order=('impl','research','bulk') if day else ('bulk','impl','research')
    return order.index(c) if c in order else len(order)

def live_tickets():
    """Live tickets, reaping those whose process is gone. Caller holds the guard."""
    out=[]
    if not queue.is_dir(): return out
    for f in queue.glob('*.json'):
        t=read_json(f)
        if not t or not alive(t.get('pid')):
            f.unlink(missing_ok=True);continue
        out.append(t)
    return out

# Aging: a ticket that has waited at least AGING[class] seconds is promoted to the front group
# (promoted tickets are ordered by enqueue time). Prevents starvation of research/bulk by a
# steady stream of short impl builds. Override for tests: SERRE_LOCK_AGING="impl=900,research=900,bulk=1800".
AGING={'impl':900,'research':900,'bulk':1800}
for part in os.environ.get('SERRE_LOCK_AGING','').split(','):
    if '=' in part:
        k,v=part.split('=',1)
        if k in AGING:
            try: AGING[k]=float(v)
            except ValueError: pass

def order_key(t,hour,now=None):
    now=time.time() if now is None else now
    c=t.get('class','impl'); enq=float(t.get('enqueued',0))
    # The coordinator's merge/registration builds always go first (11-11).
    if c=='coord': return (-1,0,enq,str(t.get('token','')))
    promoted=now-enq>=AGING.get(c,900)
    # By day bulk is never promoted: it takes the lock only when no impl/research ticket waits (11-11).
    if c=='bulk' and 8<=hour<23: promoted=False
    return (0 if promoted else 1,0 if promoted else class_rank(c,hour),enq,str(t.get('token','')))

def reap_lock():
    for slot in SLOTS:
        if slot.is_symlink(): raise RuntimeError('refuse symlink lock directory')
        if slot.exists():
            previous=read_owner(slot)
            if previous and not alive(previous.get('pid')):
                erase(slot)
            elif previous is None and time.time()-slot.stat().st_mtime>60:
                # A crash between mkdir and publication leaves no live owner.
                erase(slot)

def holders():
    return [(slot,read_owner(slot)) for slot in SLOTS if slot.exists()]

def status():
    with protected():
        reap_lock()
        hour=jst_hour()
        now=time.time()
        hs=holders()
        for slot,o in hs:
            if o and o.get('started'):
                start=datetime.datetime.fromisoformat(o['started']).astimezone(JST)
                print(f"holder[{SLOTS.index(slot)}]: {Path(o.get('worktree','?')).name} [{o.get('class','?')}] since {start:%H:%M} :: {' '.join(o.get('command',[]))[:100]}")
        if not hs: print('holder: (free)')
        print(f'capacity: {capacity(hour)}')
        ts=sorted(live_tickets(),key=lambda t:order_key(t,hour))
        print(f"queue ({'day' if 8<=hour<23 else 'night'} order): {len(ts)}")
        for i,t in enumerate(ts,1):
            up=' (繰り上げ)' if order_key(t,hour,now)[0]==0 else ''
            print(f"  {i}. {Path(t.get('worktree','?')).name} [{t.get('class')}]{up} waiting {int(now-float(t.get('enqueued',now)))//60}m :: {' '.join(t.get('command',[]))[:80]}")

if a.status:
    status();sys.exit(0)

def log_event(event):
    try:
        with history.open('a') as h:
            h.write(json.dumps({'event':event,'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                'worktree':Path(worktree).name,'class':klass,'pid':os.getpid(),'token':token,
                                'queued':queued_at,'slot':(SLOTS.index(myslot) if myslot else None),
                                'command':' '.join(a.command)[:200]},ensure_ascii=False)+'\n')
    except OSError: pass

def remove_ticket():
    global ticketed
    if ticketed:
        ticket.unlink(missing_ok=True);ticketed=False

try:
    ps=subprocess.run(['ps','-axo','command='],capture_output=True,text=True)
    if ps.returncode: print('warning: cannot inspect unguarded lake builds: '+ps.stderr.strip(),file=sys.stderr)
    else:
        lines=[l for l in ps.stdout.splitlines() if re.search(r'(?:^|[/\s])lake\s+build(?:\s|$)',l) and 'with_build_lock.sh' not in l and not re.search(r'Python - --wait|python3 - --wait',l)]
        if lines: print('warning: existing lake build (possibly unguarded):\n'+'\n'.join(lines),file=sys.stderr)
    with protected():
        queue.mkdir(exist_ok=True)
        if queue.is_symlink(): raise RuntimeError('refuse symlink queue directory')
        ticket.write_text(json.dumps({'pid':os.getpid(),'worktree':worktree,'class':klass,'enqueued':enqueued,
                                      'token':token,'command':a.command},ensure_ascii=False)+'\n')
        ticketed=True
    started=time.monotonic(); last_notice=-float('inf'); previous=None; position=None
    while not acquired:
        if interrupted: sys.exit(128+interrupted)
        with protected():
            reap_lock()
            hour=jst_hour()
            hs=holders()
            bulk_held=any(o and o.get('class')=='bulk' for _,o in hs)
            # At most one bulk holder at a time; an ineligible bulk ticket does not block the others.
            everyone=live_tickets()
            ts=[t for t in sorted(everyone,key=lambda t:order_key(t,hour))
                if not (t.get('class')=='bulk' and bulk_held)]
            tokens=[t.get('token') for t in ts]
            free=[slot for slot in SLOTS[:capacity(hour)] if not slot.exists()]
            position=tokens.index(token)+1 if token in tokens else None
            if token not in [t.get('token') for t in everyone]:
                # Our ticket vanished (e.g. reaped by mistake); republish it.
                ticket.write_text(json.dumps({'pid':os.getpid(),'worktree':worktree,'class':klass,'enqueued':enqueued,
                                              'token':token,'command':a.command},ensure_ascii=False)+'\n')
                position=None
            elif position==1 and free and len(hs)<capacity(hour):
                owner['started']=datetime.datetime.now(datetime.timezone.utc).isoformat()
                myslot=free[0]
                owner['slot']=SLOTS.index(myslot)
                myslot.mkdir()
                try: (myslot/'owner.json').write_text(json.dumps(owner,ensure_ascii=False)+'\n')
                except BaseException:
                    erase(myslot);raise
                acquired=True
                remove_ticket()
                log_event('acquire')
            if not acquired: previous=[o for _,o in hs]
        if acquired: break
        now=time.monotonic()
        if now-last_notice>=60:
            print(f'waiting for build lock [{klass}] position {position}: '+json.dumps(previous,ensure_ascii=False),file=sys.stderr,flush=True);last_notice=now
        if a.wait is not None and now-started>=a.wait:
            with protected(): remove_ticket()
            sys.exit(75)
        delay=2 if a.wait is None else min(2,max(0,a.wait-(now-started)))
        # Short sleep slices let signal cleanup run promptly.
        until=time.monotonic()+delay
        while time.monotonic()<until and not interrupted: time.sleep(max(0.0,min(.1,until-time.monotonic())))
    if interrupted: sys.exit(128+interrupted)
    child=subprocess.Popen(a.command,start_new_session=True)
    if interrupted: handle(interrupted,None)
    rc=child.wait()
    sys.exit(128+interrupted if interrupted else (128-rc if rc<0 else rc))
except (OSError,RuntimeError) as exc:
    print('with_build_lock: '+str(exc),file=sys.stderr);sys.exit(1)
finally:
    with protected():
        remove_ticket()
        if acquired:
            current=read_owner(myslot) if myslot else None
            if current and current.get('token')==token:
                erase(myslot);log_event('release')
PY
