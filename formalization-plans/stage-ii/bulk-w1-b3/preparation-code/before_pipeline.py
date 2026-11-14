from pathlib import Path
import subprocess,json,os,datetime,time
w=Path('/tmp/bulk-w1-b3');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');b=w/'before'
targets=json.load(open(w/'before-targets.json'));out=w/'before-build';out.mkdir(exist_ok=True)
for i in range(0,len(targets),96):
 p=out/f'{i//96:03}.json'
 if p.exists() and json.load(open(p))['rc']==0:continue
 while True:
  current=datetime.datetime.now()
  if 8<=current.hour<23:raise SystemExit('Night build stage paused at daytime boundary; resume after report')
  log=out/f'{i//96:03}.log';cmd=['python3','-B',str(w/'guard.py'),'--cwd',str(b),'--log',str(log),'--night-only','--seconds','1200','--','lake','--fail-fast','build',*targets[i:i+96]]
  p0=subprocess.run(cmd);receipt=json.load(open(str(log)+'.json'))
  if p0.returncode==0:p.write_text(json.dumps({'rc':0,'modules':targets[i:i+96],'resource':receipt},indent=2));break
  if p0.returncode==75 and receipt['reason']=='bounded batch':continue
  raise SystemExit(p0.returncode)
(w/'before-build-complete.json').write_text(json.dumps({'targets':len(targets),'finished':time.time()}));print('before delta build complete',len(targets),flush=True)
# Parallel compiler-reference capture, each with a single Lean thread; four jobs total.
import concurrent.futures,sys
sys.path.insert(0,str(r/'scripts/refactor'))
import bulk_collect
files=json.load(open(w/'delta-files.json'));groups=[files[i:i+12] for i in range(0,len(files),12)]
def one(item):
 index,paths=item;dest=w/'delta-captures'/f'{index:03}'
 if (dest/'files.json').exists():return
 # Retry preserves previous successful files and collects only missing ones.
 if dest.exists():
  complete={p.name for p in dest.glob('*.json')};remaining=[x for x in paths if x[:-5].replace('/','.')+'.json' not in complete]
 else:remaining=paths
 temp=dest.with_name(dest.name+'-pending')
 if temp.exists():
  import shutil;shutil.rmtree(temp)
 bulk_collect.collect(b,remaining,temp)
 dest.mkdir(parents=True,exist_ok=True)
 for p in temp.glob('*.json'):
  if p.name!='files.json':p.replace(dest/p.name)
 (dest/'files.json').write_text(json.dumps(sorted(paths)));(temp/'files.json').unlink(missing_ok=True);temp.rmdir();print('collect group',index,len(paths),flush=True)
os.environ['LEAN_NUM_THREADS']='1'
(w/'delta-captures').mkdir(exist_ok=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 for result in pool.map(one,enumerate(groups)):pass
(w/'delta-collect-complete.json').write_text(json.dumps({'files':len(files),'finished':time.time()}))
