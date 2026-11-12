"""Compare v3b fingerprints with cite projection and owned private row names.
Native captures qualify source-private references by their defining module.
Type/body hashes, axioms and kernel attributes remain checked; raw compiler
inventories remain available without ordinal pairing.
"""
from pathlib import Path
import sys,re,json,hashlib,io,contextlib,inspect
sys.path.insert(0,str(Path(__file__).resolve().parent))
import compare_snapshots as C
original=C.declaration_source
AUTHORED_AUX=set()

def projection(text):
 text=original(text);mask=C.code_only(text);edits=[]
 for m in re.finditer(r'(?:def|theorem|lemma|abbrev|opaque|class|structure|inductive|instance)\s+(?:[\w.]+\.)?«(_aux_[^»]+)»',mask):AUTHORED_AUX.add(m[1])
 for m in re.finditer(r'(?m)^(?:attribute[ \t]+\[[^\n]*|local[ \t]+(?:notation|infix|prefix|postfix)\b[^\n]*|by[ \t]*)$',mask):edits.append(m.span())
 for a,b in reversed(edits):text=text[:a]+''.join('\n' if c=='\n' else ' ' for c in text[a:b])+text[b:]
 return text

def aux(name,module,authored=()):
 if name in authored:return False
 parts=[part[1:-1] if part.startswith('«') and part.endswith('»') else part for part in name.split('.')]
 if any(p in AUTHORED_AUX for p in parts):return False
 encoded=re.escape(module.replace('.','_'))
 return any(re.fullmatch(r'_aux_'+encoded+r'___(?:macroRules|unexpand)_.+',p) for p in parts)

C.declaration_source=projection;C.notation_auxiliary=aux

def private_owned_functions():
 # Only actual private rows use owner-scoped user-name normalization. Public
 # names retain the existing v3b rules. Kernel fingerprints are still compared.
 source=inspect.getsource(C.normalized)
 old="return normalize_generated_name(rename(name, mapping), generated_modules)"
 new="return normalize_generated_name(rename(name, module_map.get('private_normalization', {}).get(module, {}) if row.get('is_private', False) else mapping), generated_modules)"
 if source.count(old)!=1:raise ValueError('Shared v3b comparator changed; review private ownership handling')
 scope=dict(vars(C));exec(compile(source.replace(old,new),'<bulk private row ownership>','exec'),scope)
 normalized=scope['normalized']
 source=inspect.getsource(C.auxiliary_groups)
 old="key = (rename(parent, mapping), target)"
 new="key = (rename(parent, module_map.get('private_normalization', {}).get(module, {}) if row.get('is_private', False) else mapping), target)"
 if source.count(old)!=1:raise ValueError('Shared auxiliary inventory changed; review private ownership handling')
 scope=dict(vars(C));exec(compile(source.replace(old,new),'<bulk private auxiliary ownership>','exec'),scope)
 return normalized,scope['auxiliary_groups']
C.normalized,C.auxiliary_groups=private_owned_functions()
RAW_COMPARE=C.compare

def parser_self_projection(snapshot):
 sources={r['module']:C.code_only(r['source']).splitlines() for r in snapshot.get('sources',[])}
 projected=dict(snapshot);rows=[];explained=[]
 for row in snapshot['declarations']:
  copy=dict(row);position=row.get('source_range') or {};line=position.get('start_line',0)
  lines=sources.get(row['module'],[])
  source_line=lines[line-1] if 0<line<=len(lines) else ''
  generated=bool(re.match(r'\s*(?:(?:local|scoped)\s+)?(?:notation\d*|infixl?|infixr|prefix|postfix|syntax)\b',source_line))
  if generated and row.get('is_private') is True and row.get('private_parser_descr') is True and isinstance(row.get('parser_self_body_hash'),str):
   explained.append({'module':row['module'],'name':row['name'],'kernel_name':row.get('kernel_name'),'source_line':line,'raw_body_hash':row.get('body_hash'),'parser_self_body_hash':row['parser_self_body_hash'],'content':{k:row.get(k) for k in ['kind','type_hash','parser_self_body_hash','axioms','attributes']}})
   continue
  rows.append(copy)
 projected['declarations']=rows
 return projected,explained

def compare_with_parser_companion(before,after,*args,**kwargs):
 left,a=parser_self_projection(before);right,b=parser_self_projection(after)
 module_map=(args[1] if len(args)>1 else kwargs.get('module_map')) or {}
 modules=module_map.get('modules',module_map)
 before_owners={r['module'] for r in before.get('sources',[])}
 origins={}
 for old,new in modules.items():
  if isinstance(new,str):origins.setdefault(new,set()).add(old)
 for old,rows in module_map.get('declarations',{}).items():
  for new in rows.values():origins.setdefault(new,set()).add(old)
 def groups(rows,is_after):
  result={}
  for r in rows:
   possible=origins.get(r['module'],set())&before_owners if is_after else {r['module']}
   if not possible:possible={r['module']}
   if len(possible)!=1:raise ValueError('Ambiguous original owner for compiler parser: '+r['module'])
   owner=next(iter(possible));key=json.dumps(r['content'],sort_keys=True,separators=(',',':'))
   result.setdefault(owner,{})[key]=r['content']
  return result
 aa,bb=groups(a,False),groups(b,True)
 result=RAW_COMPARE(left,right,*args,**kwargs)
 differences=[]
 for owner in sorted(aa.keys()|bb.keys()):
  x,y=aa.get(owner,{}),bb.get(owner,{})
  if x.keys()!=y.keys():
   differences.append({'name':'<source-verified notation parser descriptors>','module':owner,'change':'body','compiler_group':True,'before_sha256':hashlib.sha256(json.dumps(sorted(x)).encode()).hexdigest(),'after_sha256':hashlib.sha256(json.dumps(sorted(y)).encode()).hexdigest()})
 result['changes'].extend(differences)
 if differences:result['status']='FAIL'
 result['parser_self_identity_companions']={'policy':'Only native-typed private ParserDescr constants at verified notation commands; compare every distinct type/body/axiom/attribute payload per original source owner after replacing only its own literal Name. Repeated identical compiler descriptors caused by a reviewed split are recorded without ordinal pairing. Raw body hashes and inventories are retained.','before':a,'after':b,'before_content_groups':sum(map(len,aa.values())),'after_content_groups':sum(map(len,bb.values())),'differences':differences}
 return result
C.compare=compare_with_parser_companion

def main():
 with contextlib.redirect_stdout(io.StringIO()) as captured:
  status=C.main()
 output=captured.getvalue()
 if status in (0,1) and '--output' in sys.argv:
  result=json.loads(output)
  print(json.dumps({k:result[k] for k in ['status','before_count','after_count','parent_count']} | {'changes':len(result['changes'])}))
 elif output:
  print(output,end='')
 return status

if __name__=='__main__':sys.exit(main())
