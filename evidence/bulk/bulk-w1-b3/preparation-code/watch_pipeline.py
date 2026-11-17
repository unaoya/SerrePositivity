from pathlib import Path
import subprocess,os,time,signal,json,datetime
w=Path('/tmp/bulk-w1-b3');suffix=' -B /tmp/bulk-w1-b3/before_pipeline.py'
matches=[]
for line in subprocess.check_output(['ps','-axo','pid,command'],text=True).splitlines()[1:]:
 p,_,command=line.strip().partition(' ')
 if command.endswith(suffix):matches.append(int(p))
assert len(matches)==1,matches
root=matches[0];peak=0;reason=None
(w/'before-pipeline-pid.json').write_text(json.dumps({'pid':root,'watchdog':os.getpid()}))
while True:
 rows={}
 for line in subprocess.check_output(['ps','-axo','pid,ppid,rss'],text=True).splitlines()[1:]:
  try:p,pp,rss=map(int,line.split());rows[p]=(pp,rss*1024)
  except ValueError:continue
 if root not in rows:break
 descendants={root}
 while True:
  new={p for p,(pp,rss) in rows.items() if pp in descendants}
  if new<=descendants:break
  descendants|=new
 rss=sum(rows.get(p,(0,0))[1] for p in descendants);peak=max(peak,rss)
 now=datetime.datetime.now()
 if rss>32*1024**3:reason='32 GiB total pipeline RSS'
 elif 8<=now.hour<23:reason='daytime boundary: heavy four-job pipeline'
 if reason:
  for pid in sorted(descendants,reverse=True):
   try:os.kill(pid,signal.SIGTERM)
   except ProcessLookupError:pass
  time.sleep(2)
  for pid in sorted(descendants,reverse=True):
   try:os.kill(pid,signal.SIGKILL)
   except ProcessLookupError:pass
  break
 time.sleep(2)
(w/'before-pipeline-watch.json').write_text(json.dumps({'pid':root,'maximum_tree_rss':peak,'reason':reason,'finished':time.time()},indent=2));print('pipeline monitor finished',reason,peak,flush=True)
