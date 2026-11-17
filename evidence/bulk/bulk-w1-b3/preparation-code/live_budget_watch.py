"""Enforce the decimal 32 GB aggregate limit on the already-running night tree."""
import os,subprocess,time,signal,json,datetime,argparse
from pathlib import Path
parser=argparse.ArgumentParser();parser.add_argument('--root-pid',type=int,default=87410);parser.add_argument('--output',default='live-budget-watch.json');args=parser.parse_args()
root=args.root_pid;w=Path('/tmp/bulk-w1-b3');peak=0;peak_jobs=0;reason=None;stopping=False
def stop_requested(*_):
 global stopping
 stopping=True
signal.signal(signal.SIGTERM,stop_requested)
while not stopping:
 rows={}
 for s in subprocess.check_output(['ps','-axo','pid,ppid,rss,comm'],text=True).splitlines()[1:]:
  try:
   i,p,r,c=s.split(None,3);rows[int(i)]=(int(p),int(r)*1024,Path(c).name)
  except ValueError:pass
 if root not in rows:break
 tree={root}
 while True:
  added={i for i,(p,r,c) in rows.items() if p in tree}
  if added<=tree:break
  tree|=added
 rss=sum(rows[i][1] for i in tree|{os.getpid()} if i in rows);jobs=sum(rows[i][2] in ('lean','snapshot') and rows[i][1]>16*1024**2 for i in tree)
 peak=max(peak,rss);peak_jobs=max(peak_jobs,jobs)
 if rss>32_000_000_000 or jobs>4:
  reason='aggregate exceeds decimal 32 GB or four heavy jobs'
  for i in sorted(tree-{os.getpid()},reverse=True):
   try:os.kill(i,signal.SIGTERM)
   except ProcessLookupError:pass
  break
 time.sleep(2)
(w/args.output).write_text(json.dumps({'root_pid':root,'peak_process_tree_rss_bytes':peak,'peak_heavy_jobs':peak_jobs,'reason':reason,'finished':datetime.datetime.now().isoformat()},indent=2))
