from pathlib import Path
import subprocess,json,hashlib,re,collections,difflib
w=Path('/tmp/bulk-b3prime');r=Path('/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity-kerodon-layout');d=w/'B4';base='391b2a0d2';tip=subprocess.check_output(['git','rev-parse','main'],cwd=r,text=True).strip()
run=lambda args:subprocess.check_output(args,cwd=r)
paths=run(['git','diff',base,tip,'--name-only','--','SerrePositivity','SerrePositivity.lean','scripts','lakefile.toml','lake-manifest.json','lean-toolchain']).decode().splitlines();ours=set(run(['git','diff',base,'HEAD','--name-only']).decode().splitlines());requests=[ref+':'+p for p in paths for ref in (tip,base)];raw=subprocess.run(['git','cat-file','--batch'],input=('\n'.join(requests)+'\n').encode(),cwd=r,stdout=subprocess.PIPE,check=True).stdout;blobs={};pos=0
for q in requests:
 end=raw.index(b'\n',pos);head=raw[pos:end].decode();pos=end+1
 if head.endswith(' missing'):blobs[q]=None;continue
 sha,kind,size=head.split();assert kind=='blob';size=int(size);blobs[q]=raw[pos:pos+size];pos+=size+1
assert pos==len(raw)
mods=json.loads((d/'module-map.json').read_text());rows=json.loads((d/'namespace-rewrite-map.json').read_text())['rows'];names={x['old'] for x in rows if x['old']!=x['new']};pattern=re.compile(r'(?<![\w\'])('+ '|'.join(re.escape(s) for s in sorted(set(mods)|names,key=len,reverse=True))+r')(?![\w\'])');out=[];files=[]
for p in paths:
 src=blobs[tip+':'+p]
 if src is None:out.append({'path':p,'deleted_in_main':True});continue
 lines=src.decode().splitlines();old=blobs[base+':'+p];oldlines=old.decode().splitlines() if old is not None else [];added=set()
 for tag,a,b,c,e in difflib.SequenceMatcher(None,oldlines,lines,autojunk=False).get_opcodes():
  if tag in ('replace','insert'):added.update(range(c,e))
 hits=[{'line':i+1,'name':m.group(1),'new_main_line':i in added} for i,line in enumerate(lines) for m in pattern.finditer(line)]
 out.append({'path':p,'source_sha256':hashlib.sha256(src).hexdigest(),'new_main_lines':len(added),'literal_old_names_or_modules':hits})
 if p.endswith('.lean') and (p=='SerrePositivity.lean' or p.startswith('SerrePositivity/')):files.append(p)
(d/'main-increment-files.json').write_text(json.dumps(files,ensure_ascii=False,indent=2))
preview=(w/'main-integration-merge-tree.txt').read_text();conflicts=sorted(set(re.findall(r'(?m)^100\d+ [0-9a-f]+ [123]\t(.+)$',preview)))
result={'base_in_verified_branch':base,'verified_head':'107d005583fe01dc50b97945f0586063458e48af','main_head':tip,'core_script_delta_paths':len(paths),'areas':dict(collections.Counter('/'.join(p.split('/')[:2]) for p in paths)),'BS_body_changes':[p for p in paths if p.startswith('SerrePositivity/BhattScholze/')],'overlap_with_B3prime':sorted(set(paths)&ours),'merge_tree_conflicts':conflicts,'core_collect_candidates':len(files),'new_line_literal_hits':sum(sum(x['new_main_line'] for x in row.get('literal_old_names_or_modules',[])) for row in out),'new_line_literal_hit_files':[row['path'] for row in out if any(x['new_main_line'] for x in row.get('literal_old_names_or_modules',[]))],'scope':'Read-only main increment handoff, not merged into the verified branch. Broad candidate list includes short-name uses and is not a confirmed rewrite count. No claim that the merged main tree has passed this branch full verify.','files':out}
assert not result['BS_body_changes'];(d/'main-increment-handoff.json').write_text(json.dumps(result,ensure_ascii=False,indent=2));(d/'main-integration-merge-tree.txt').write_text(preview)
print({k:v for k,v in result.items() if k!='files'})
