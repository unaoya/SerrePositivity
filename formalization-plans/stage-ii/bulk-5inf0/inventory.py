from pathlib import Path
import json,re,sys,hashlib,collections,subprocess,argparse
parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[3]);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args();R=args.root.resolve();W=args.output;W.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(R/'scripts/refactor'));from layer_check import code_only
DECL=re.compile(r'^(?:@\[[^\n]*?\]\s*)*(?P<mods>(?:(?:private|public|protected|noncomputable|unsafe|local|scoped)\s+)*)(?P<kind>def|abbrev|theorem|lemma|structure|class|instance|opaque|inductive)\b\s*(?P<name>[\w\u0080-\uffff][\w\u0080-\uffff\'.]*)?')
def scan(path):
 text=path.read_text();mask=code_only(text);lines=mask.splitlines();original=text.splitlines();namespace='';stack=[];decls=[]
 for i,line in enumerate(lines):
  if not line or line[0].isspace():continue
  core=re.sub(r'^(?:@\[[^\n]*?\]\s*)*','',line).strip();scope=re.match(r'(?:(?:public|noncomputable)\s+)*section\b',core)
  if core.startswith('namespace '):
   part=core.split()[1];stack.append(namespace);namespace=part.removeprefix('_root_.') if part.startswith('_root_.') else '.'.join(filter(None,[namespace,part]));continue
  if scope:stack.append(namespace);continue
  if re.match(r'^end(?:\s|$)',core):
   if stack:namespace=stack.pop()
   continue
  m=DECL.match(line)
  if not m:continue
  short=m['name'];full=None if short is None or (m['kind']=='instance' and short in ['where']) else short.removeprefix('_root_.') if short.startswith('_root_.') else '.'.join(filter(None,[namespace,short]));end=i+1
  while end<len(lines) and (not lines[end] or lines[end][0].isspace()):end+=1
  block='\n'.join(original[i:end]);code='\n'.join(lines[i:end]);header=re.split(r':=|\bwhere\b',code,maxsplit=1)[0].strip();decls.append({'name':full,'leaf':short,'kind':m['kind'],'private':'private' in m['mods'].split(),'line':i+1,'lines':end-i,'signature_source':header,'sorry_tokens':len(re.findall(r'\bsorry\b',code))})
 return {'path':str(path.relative_to(R)),'lines':len(original),'sha256':hashlib.sha256(text.encode()).hexdigest(),'sorry_tokens':len(re.findall(r'\bsorry\b',mask)),'declarations':decls}
main={};leaf=collections.defaultdict(list)
for root in ['BhattScholze','HomologicalAlgebra','CommutativeAlgebra','EInfinity/Interface','EInfinity/Perfectoidization']:
 for path in (R/'SerrePositivity'/root).rglob('*.lean'):
  for d in scan(path)['declarations']:
   if d['name']:
    item={'name':d['name'],'path':str(path.relative_to(R)),'line':d['line'],'signature_source':d['signature_source']};main.setdefault(d['name'],[]).append(item);leaf[d['leaf']].append(item)
drafts=[scan(p) for p in sorted((R/'formalization-plans/bhatt-scholze/drafts').glob('A*/*.lean'))]
for file in drafts:
 for d in file['declarations']:
  d['same_full_name_candidates']=main.get(d['name'],[]);d['same_leaf_candidates']=leaf.get(d['leaf'],[])
summary={'base_main':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'scope':'A0-A9 only; syntactic source inventory, candidates are not automatic deletion decisions','files':len(drafts),'source_lines':sum(x['lines'] for x in drafts),'sorry_tokens':sum(x['sorry_tokens'] for x in drafts),'named_declarations':sum(d['name'] is not None for f in drafts for d in f['declarations']),'same_full_name_candidates':sum(bool(d['same_full_name_candidates']) for f in drafts for d in f['declarations']),'file_rows':[{'path':f['path'],'lines':f['lines'],'decls':len(f['declarations']),'sorry':f['sorry_tokens'],'same_full_name':sum(bool(d['same_full_name_candidates']) for d in f['declarations'])} for f in drafts]}
(W/'draft-source-inventory.json').write_text(json.dumps(drafts,ensure_ascii=False,indent=2));(W/'draft-inventory-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2));print({k:v for k,v in summary.items() if k!='file_rows'});print('\n'.join(str(x) for x in summary['file_rows']))
