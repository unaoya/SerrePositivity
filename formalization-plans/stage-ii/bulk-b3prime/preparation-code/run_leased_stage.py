from pathlib import Path
import datetime,subprocess,sys,json,time
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');stage=sys.argv[1];specs={'targets':('target_slot.py','target-build/complete.json',[]),'preservation':('preserve_slot.py','preservation/complete.json',[]),'citations-before':('citation_slot.py','citation-metadata/before/complete.json',['before']),'citations-after':('citation_slot.py','citation-metadata/after/complete.json',['after'])};script,completion,prefix_args=specs[stage];i=0
assert (W/'before/complete.json').exists(),'baseline capture worker must finish first'
while not (W/completion).exists():
 now=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=9)));budget=1650 if now.hour>=23 or now.hour<8 else 270
 with (W/f'{stage}-lease-{i:03}.log').open('a') as log:r=subprocess.run(['zsh',str(R/'scripts/refactor/with_build_lock.sh'),'--wait','3600','--class','bulk','--','gtimeout','--kill-after=5s',str(budget+5),'python3',str(W/script),*prefix_args,str(budget)],cwd=R,stdout=log,stderr=subprocess.STDOUT)
 record={'stage':stage,'lease':i,'rc':r.returncode,'budget':budget,'queued_time':now.isoformat()};(W/(stage+'-driver-progress.json')).write_text(json.dumps(record));print(record,flush=True)
 if r.returncode not in [0,75]:raise SystemExit(r.returncode)
 i+=1
print(stage,'COMPLETE',flush=True)
