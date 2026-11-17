from pathlib import Path
import json,subprocess,hashlib,re,sys,copy,time
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');B=W/'final-bundle';D=R/'evidence/bulk/bulk-b3prime';manifest=json.loads((B/'manifest.json').read_text());apply='--apply' in sys.argv
assert (W/'preparation-complete.json').exists(),'all isolated preparation gates required';prep=json.loads((W/'preparation-complete.json').read_text());assert prep['source_manifest_sha256']==hashlib.sha256((B/'manifest.json').read_bytes()).hexdigest();assert prep['preservation']['unexplained']==0 and not prep['citation_comparison']['missing'] and not prep['citation_comparison']['extra']
main=subprocess.check_output(['git','rev-parse','main'],cwd=R,text=True).strip()
if apply:subprocess.run(['git','merge-base','--is-ancestor',main,'HEAD'],cwd=R,check=True)
assert not subprocess.check_output(['git','diff','HEAD','--name-only','--','SerrePositivity','SerrePositivity.lean','scripts'],cwd=R,text=True).strip(),'source tree must be clean before application'
original={m.replace('.','/')+'.lean' for m in json.loads((D/'stage0-import-closure.json').read_text())['reverse_closure']}|{m.replace('.','/')+'.lean' for m in json.loads((W/'additional-doc-modules.json').read_text())};einf='SerrePositivity/EInfinity.lean';problems=[]
for p in sorted(original):
 baseline=subprocess.check_output(['git','show','32d364b53:'+p],cwd=R)
 if p!=einf and (not (R/p).exists() or (R/p).read_bytes()!=baseline):problems.append({'path':p,'reason':'main changed a prepared original source; reconcile before applying'})
changes={}
for m,sha in manifest['files'].items():
 p=m.replace('.','/')+'.lean';data=(B/p).read_bytes();assert hashlib.sha256(data).hexdigest()==sha
 if p not in original and (R/p).exists() and (R/p).read_bytes()!=data:problems.append({'path':p,'reason':'new destination collision'})
 changes[p]=data
# The only prepared source changed in incoming main is the import-only EInfinity
# aggregate. Preserve every incoming line except the four approved BS specializations.
special=[r for r in json.loads((D/'module-map.proposed.json').read_text())['rows'] if r['old_module'].startswith('SerrePositivity.EInfinity.Perfectoidization.')];text=(R/einf).read_text();removed=[]
for row in special:
 for name in [row['old_module'],row['new_module']]:
  pattern=re.compile(r'(?m)^public import '+re.escape(name)+r'[ \t]*\n');text,n=pattern.subn('',text)
  if n:removed.append(name)
changes[einf]=text.encode()
baseline_einf=subprocess.check_output(['git','show','32d364b53:'+einf],cwd=R,text=True)
expected_removed={r['old_module'] for r in special if re.search(r'(?m)^public import '+re.escape(r['old_module'])+r'[ \t]*$',baseline_einf)}
assert set(removed)==expected_removed,(removed,expected_removed)
assert all(not re.search(r'(?m)^public import '+re.escape(r[k])+r'[ \t]*$',text) for r in special for k in ['old_module','new_module'])
# Preflight actual audit sources before changing any file.
audit=json.loads((W/'audit-bundle/manifest.json').read_text());assert audit['source_main']==main,'refresh audit preview against current main'
for row in audit['changed']:
 p=row['path'];assert hashlib.sha256((R/p).read_bytes()).hexdigest()==row['before_sha256'],p;data=(W/'audit-bundle'/p).read_bytes();assert hashlib.sha256(data).hexdigest()==row['after_sha256'];changes[p]=data
for row in json.loads((W/'draft-header-plan.json').read_text())['rows']:
 p=row['path'];assert hashlib.sha256((R/p).read_bytes()).hexdigest()==row['source_sha256'],p;data=(W/'draft-header-bundle'/p).read_bytes();assert hashlib.sha256(data).hexdigest()==row['preview_sha256'];changes[p]=data
full=json.loads((R/'scripts/refactor/layers.json').read_text());old=copy.deepcopy(full['klw1']);added={}
for file in ['new-main-tiers.json','main-increment-tiers.json']:
 for m,row in json.loads((W/file).read_text()).items():
  if m in full['klw1']['modules']:assert full['klw1']['modules'][m]==row['tier'],m
  else:full['klw1']['modules'][m]=row['tier'];added[m]=row
m='SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialValueCone'
if m in full['klw1']['modules']:assert full['klw1']['modules'][m]=='Portable'
else:full['klw1']['modules'][m]='Portable';added[m]={'tier':'Portable','rule':'new generic cofinality module independent of implementation/Entrypoints'}
assert all(full['klw1'][k]==v for k,v in old.items() if k!='modules');assert all(full['klw1']['modules'][m]==v for m,v in old['modules'].items());changes['scripts/refactor/layers.json']=(json.dumps(full,ensure_ascii=False,indent=2)+'\n').encode()
if problems:(W/'application-preflight-problems.json').write_text(json.dumps(problems,ensure_ascii=False,indent=2));raise SystemExit(str(problems))
receipt={'status':'applied' if apply else 'preflight only','main':main,'source_baseline':'32d364b53','paths_written':{p:hashlib.sha256(data).hexdigest() for p,data in changes.items()},'delete_paths':manifest['delete_paths'],'main_EInfinity_imports_preserved_except':removed,'new_tier_entries':added,'existing_tiers_changed':0,'exceptions_changed':0,'formal_audits_changed':len(audit['changed']),'time':time.time()}
if apply:
 for p in manifest['delete_paths']:assert p not in changes;(R/p).unlink()
 for p,data in changes.items():target=R/p;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
(W/('actual-application.json' if apply else 'actual-application-preflight.json')).write_text(json.dumps(receipt,ensure_ascii=False,indent=2));print(receipt['status'],'writes',len(changes),'deletes',len(manifest['delete_paths']),'tier additions',len(added))
