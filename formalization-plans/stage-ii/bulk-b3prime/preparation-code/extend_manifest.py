from pathlib import Path
import re,json,sys
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');W=Path('/tmp/bulk-b3prime');D=R/'formalization-plans/stage-ii/bulk-b3prime';sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
p=W/'before-manifest.json';old=json.loads(p.read_text());ns=json.loads((D/'namespace-map.proposed.json').read_text())['rows'];closure=json.loads((D/'stage0-import-closure.json').read_text())['reverse_closure'];leaves={r['old'].rsplit('.',1)[-1] for r in ns if r['old']!=r['new']};rx=re.compile(r"(?<![\w'])"+'(?:'+'|'.join(map(re.escape,sorted(leaves,key=len,reverse=True)))+r")(?![\w'])");owners={r['old_module'] for r in ns};modules=set(old['modules']);refs=set(old['reference_files']);skipped={r['module'] for r in old['import_only_modules']}
for m in closure:
 path=m.replace('.','/')+'.lean';text=code_only((R/path).read_text());body=re.sub(r'(?m)^\s*(?:(?:public|private|meta)\s+)*import[^\n]*','',text);body=re.sub(r'(?m)^\s*module\s*$','',body)
 if not body.strip():continue
 modules.add(m)
 if m in owners or rx.search(text):refs.add(path)
extra=sorted(modules-set(old['modules']));old['modules']+=extra;old['groups']+=[extra[i:i+8] for i in range(0,len(extra),8)];old['reference_files']=sorted(refs);old['manifest_extension']='R8-8 complete20 Derived namespace coverage; preserve prior group IDs and captures; append new modules only';p.write_text(json.dumps(old,ensure_ascii=False,indent=2)+'\n');print('modules',len(modules),'refs',len(refs),'appended',len(extra));print(extra)
