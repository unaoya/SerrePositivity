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
