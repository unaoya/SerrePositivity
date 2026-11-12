"""Compare unchanged fingerprints using a source projection for new cite metadata.
Only source-authorship parsing changes: fingerprints/axioms/kernel attributes and
original generated-name inventories are retained verbatim.
"""
from pathlib import Path
import sys,re,json,hashlib,io,contextlib
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
