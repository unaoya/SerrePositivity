"""Run B3 commands in their own process group, inside the shared bulk build ticket."""
import argparse,datetime,json,os,signal,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--cwd',required=True);p.add_argument('--log',required=True);p.add_argument('--seconds',type=int,default=900);p.add_argument('--night-only',action='store_true');p.add_argument('--jobs',type=int,default=4);p.add_argument('--threads',type=int);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args();cmd=a.command[1:] if a.command[:1]==['--'] else a.command
now=datetime.datetime.now();night=now.hour>=23 or now.hour<8
if a.night_only and not night:raise SystemExit(75)
assert 1<=a.jobs<=16
env=dict(os.environ,LEAN_NUM_THREADS=str(a.threads) if a.threads else ('4' if night else '2'))
out=Path(a.log);out.parent.mkdir(parents=True,exist_ok=True);start=time.monotonic();peak=0;peak_lean_jobs=0;reason=None;known=set()
with out.open('w') as log:
 proc=subprocess.Popen(cmd,cwd=a.cwd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  rows={}
  for line in subprocess.check_output(['ps','-axo','pid,ppid,rss,comm'],text=True).splitlines()[1:]:
   try:
    a0,a1,a2,comm=line.split(None,3);i,parent,rss=map(int,[a0,a1,a2]);rows[i]=(parent,rss*1024,Path(comm).name)
   except ValueError:continue
  children={proc.pid}
  while True:
   new={i for i,(parent,rss,comm) in rows.items() if parent in children}
   if new<=children:break
   children|=new
  known|=children;peak=max(peak,sum(rows.get(i,(0,0,''))[1] for i in children));peak_lean_jobs=max(peak_lean_jobs,sum(rows.get(i,(0,0,''))[2] in ('lean','snapshot') and rows.get(i,(0,0,''))[1]>16*1024**2 for i in children))
  current=datetime.datetime.now()
  if peak>32_000_000_000:reason='memory budget 32 GB'
  elif peak_lean_jobs>a.jobs:reason=f'more than {a.jobs} heavy Lean or snapshot processes'
  elif time.monotonic()-start>a.seconds:reason='bounded batch'
  elif a.night_only and 8<=current.hour<23:reason='daytime boundary'
  if reason:
   for pid in sorted(children,reverse=True):
    try:os.kill(pid,signal.SIGTERM)
    except ProcessLookupError:pass
   time.sleep(2)
   for pid in sorted(children,reverse=True):
    try:os.kill(pid,signal.SIGKILL)
    except ProcessLookupError:pass
   break
  time.sleep(2)
 rc=proc.wait()
record={'command':cmd,'cwd':a.cwd,'rc':rc,'reason':reason,'seconds':time.monotonic()-start,'peak_process_tree_rss_bytes':peak,'peak_lean_or_snapshot_jobs':peak_lean_jobs,'threads':env['LEAN_NUM_THREADS'],'heavy_job_limit':a.jobs,'started_local':now.isoformat(),'finished_local':datetime.datetime.now().isoformat()}
out.with_suffix(out.suffix+'.json').write_text(json.dumps(record,indent=2));print(json.dumps(record),flush=True)
raise SystemExit(75 if reason else rc)
