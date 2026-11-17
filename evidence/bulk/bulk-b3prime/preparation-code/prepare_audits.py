from pathlib import Path
import json,re,subprocess,hashlib
W=Path('/tmp/bulk-b3prime');R=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');out=W/'audit-bundle';out.mkdir(exist_ok=True);plan=json.loads((W/'preservation-module-plan.json').read_text());modules=plan['modules'];deleted='SerrePositivity.Inputs.Perfectoidization';surrogate='SerrePositivity.BhattScholze.Perfectoidization.Interface.IntegralExistence';names=json.loads((W/'public-comparison-name-map.json').read_text());names['SerrePositivity.Inputs.exists_perfectoidization_of_finite']='SerrePositivity.BhattScholze.exists_perfectoidization_of_finite';name_rx=re.compile(r'(?<![\w])(?:'+'|'.join(re.escape(n) for n in sorted(names,key=len,reverse=True))+r")(?![\w'])");import_rx=re.compile(r'(?m)^(?:(?:public|private|meta)\s+)*import\s+(SerrePositivity(?:\.[\w]+)*)');mod_sets=re.compile(r'(?ms)(\blet\s+mods\b[^=]*:=\s*(?:Std\.HashSet\.ofList\s*)?#?\[)(.*?)(\])');quote=re.compile(r'`(SerrePositivity(?:\.[\w]+)*)');records=[];main=subprocess.check_output(['git','rev-parse','main'],cwd=R,text=True).strip();paths=subprocess.check_output(['git','ls-tree','-r','--name-only',main,'--','scripts'],cwd=R,text=True).splitlines();paths=sorted(p for p in paths if p.endswith('.lean') and (re.fullmatch(r'scripts/audit_[^/]+\.lean',p) or p.startswith('scripts/audit/')))
def owners(m):
 if m==deleted:return []
 return sorted({modules.get(m,m)}|set(plan.get('declarations',{}).get(m,{}).values()))
for path in paths:
 original=subprocess.check_output(['git','show',main+':'+path],cwd=R,text=True);text=original;sets=[];protected=[]
 def transport(match):
  inner=match[2];old=quote.findall(inner);assert old and not quote.sub('',inner).replace(',','').strip(),(path,'module list has nonliteral expression');new=list(dict.fromkeys(n for m in old for n in owners(m)));sets.append({'old_modules':old,'new_modules':new,'additions':sorted(set(new)-set(old)),'deleted_wrapper_module':deleted in old});body=match[1]+', '.join('`'+m for m in new)+match[3];marker='__B3PRIME_AUDIT_MODULE_SET_'+str(len(protected))+'__';protected.append(body);return marker
 text=mod_sets.sub(transport,text)
 # Imports are module names, not declaration names; protect before name changes.
 imports=[]
 def imp(match):
  old=match[1];new=modules.get(old,surrogate if old==deleted else old);marker='__B3PRIME_AUDIT_IMPORT_'+str(len(imports))+'__';imports.append(match[0][:-len(old)]+new);return marker
 text=import_rx.sub(imp,text);text=name_rx.sub(lambda m:names[m[0]],text)

 short=json.loads((W/'audit-short-name-plan.json').read_text())['files'].get(path,{})
 if short:
  import sys
  sys.path.insert(0,str(R/'scripts/refactor'))
  from layer_check import code_only
  clean=code_only(text);edits=[]
  for leaf,row in short.items():
   for match in re.finditer(r"(?<![\w.])"+re.escape(leaf)+r"(?![\w'])",clean):
    edits.append((match.start(),match.end(),'_root_.'+row['new']))
  for start,end,new_name in sorted(edits,reverse=True):text=text[:start]+new_name+text[end:]

 for i,body in enumerate(protected):text=text.replace('__B3PRIME_AUDIT_MODULE_SET_'+str(i)+'__',body)
 for i,body in enumerate(imports):text=text.replace('__B3PRIME_AUDIT_IMPORT_'+str(i)+'__',body)
 if path=='scripts/audit_einfinity.lean':
  moved_einf={row['new_module'] for row in json.loads((W/'B4/public-owner-map.json').read_text())['rows'] if row['old_module'].startswith('SerrePositivity.EInfinity.Perfectoidization.')}
  assert len(moved_einf)==4,moved_einf
  text=text.replace('import SerrePositivity.EInfinity\n','import SerrePositivity.EInfinity\n'+''.join('import '+m+'\n' for m in sorted(moved_einf)),1)
 if text!=original:
  p=out/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text);records.append({'path':path,'source_main':main,'before_sha256':hashlib.sha256(original.encode()).hexdigest(),'after_sha256':hashlib.sha256(text.encode()).hexdigest(),'module_scope_transport':sets,'logic_policy':'Only declaration/import identifiers and module membership transported; no predicate, axiom allowlist, traversal, or failure condition changed. Extracted owners added to preserve original coverage.'})
summary={'source_main':main,'discovered_formal_audits':len(paths),'changed':records,'status':'isolated audit followup preview only; actual application and formal execution pending'};(out/'manifest.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print('formal audits',len(paths),'followup changed',len(records),'module-set transports',sum(len(r['module_scope_transport']) for r in records))
