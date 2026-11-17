from pathlib import Path
import json,re,subprocess,hashlib
R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity');W=Path('/tmp/bulk-b3prime');plan=json.loads((W/'namespace-rewrite-plan.json').read_text());rows=plan['rows'];names={r['old']:r['new'] for r in rows if r['old']!=r['new'] and not r['old'].startswith('_private.')};mods=plan['modules'];lookup=mods|names;rx=re.compile(r'(?<![\w.])(?:'+'|'.join(re.escape(n) for n in sorted(lookup,key=len,reverse=True))+r")(?![\w'])");head=subprocess.check_output(['git','rev-parse','main'],cwd=R,text=True).strip();files=subprocess.check_output(['git','diff','--name-only','32d364b53',head,'--','SerrePositivity','SerrePositivity.lean','scripts'],cwd=R,text=True).splitlines();hits=[]
for f in files:
 p=R/f
 if not p.exists():continue
 text=p.read_text()
 for match in rx.finditer(text):hits.append({'path':f,'line':text.count('\n',0,match.start())+1,'old':match[0],'new':lookup[match[0]],'text':text.splitlines()[text.count('\n',0,match.start())]})
result={'baseline':'32d364b53','main':head,'changed_code_paths':len(files),'affected_paths':len({r['path'] for r in hits}),'hits':hits,'status':'Read-only text impact, not Lean resolution. Merge/recollect incremental users immediately before actual application; retain main EInfinity aggregate added imports.'};(W/'main-increment-impact.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));print('changed',len(files),'affected',result['affected_paths'],'hits',len(hits));print(sorted({r['path'] for r in hits}))
