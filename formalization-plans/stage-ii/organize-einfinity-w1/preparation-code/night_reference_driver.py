"""Wait outside the shared lease, then collect the two original formal audits at night.
This does not apply the preview or edit mathematical sources.
"""
from pathlib import Path
import argparse,datetime,json,os,subprocess,sys,time,zoneinfo
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);a=p.parse_args();root=a.root.resolve();code=Path(__file__).resolve().parent;before=Path('/private/tmp/oe-w1-before-30ae8948f');out=Path('/private/tmp/oe-w1-refs-before');state=out/'night-driver.json';(out/'night-driver.pid').write_text(str(os.getpid())+'\n');progress=json.loads((out/'progress.json').read_text());assert progress['complete'] and progress['completed_files']==824;assert json.loads(Path('/private/tmp/oe-w1-native-plan/completed-preview/review.json').read_text())=={}
def record(**kw):state.write_text(json.dumps(dict(pid=os.getpid(),updated_jst=datetime.datetime.now(zoneinfo.ZoneInfo('Asia/Tokyo')).isoformat(),**kw),indent=2)+'\n')
print('Waiting outside the lease for the night window',flush=True);record(phase='waiting-outside-lease')
while True:
 if (out/'pause-night-driver').exists():record(phase='paused-before-lease');raise SystemExit(76)
 now=datetime.datetime.now(zoneinfo.ZoneInfo('Asia/Tokyo'))
 if now.hour>=23 or now.hour<8:break
 time.sleep(60)
for path in ['scripts/audit_einfinity.lean','scripts/audit_bhatt_scholze_stage2.lean']:
 if (out/'pause-night-driver').exists():record(phase='paused-before-lease');raise SystemExit(76)
 label=Path(path).stem;log=out/(label+'-original-night-guard.log');cmd=['zsh','scripts/refactor/with_build_lock.sh','--class','bulk','--wait','3600','--','python3',str(code/'process_guard.py'),'--cwd',str(before),'--log',str(log),'--night-only','--seconds','1650','--jobs','1','--threads','1','--','python3',str(code/'audit_reference_slot.py'),'--root',str(before),'--tools',str(root/'scripts/refactor'),'--output',str(out),'--file',path,'--budget','1600'];record(phase='queued-or-collecting-original-audit',audit=path);print('Queueing one original audit',path,flush=True)
 with (out/(label+'-original-night-lease.log')).open('w') as f:r=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
 print('Released original audit',path,r.returncode,flush=True)
 if r.returncode:record(phase='stopped-on-audit-capture',audit=path,returncode=r.returncode);raise SystemExit(r.returncode)
r=subprocess.run([sys.executable,str(code/'preview_completed.py'),'--root',str(before),'--tools',str(root/'scripts/refactor'),'--captures',str(out/'captures'),'--plan',str(root/'formalization-plans/stage-ii/organize-einfinity-w1/namespace-rewrite-map.json'),'--output','/private/tmp/oe-w1-native-plan/completed-preview'],cwd=root);record(phase='original-audits-and-preview-complete' if r.returncode==0 else 'stopped-for-preview-review',returncode=r.returncode);raise SystemExit(r.returncode)
