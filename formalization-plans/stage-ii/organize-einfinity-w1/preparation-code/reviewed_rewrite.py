"""Retain B3 guards; allow only individually recorded anonymous-instance spellings."""
from pathlib import Path
import gzip,hashlib,inspect,json
import bulk_namespace as B
import klw1_namespace as K
HERE=Path(__file__).resolve().parent.parent
OLD='''                normal = old_text.removeprefix("_root_.")'''
NEW='''                if old_text == "instance" and (module, ref["name"], a, b) in reviewed_anonymous_binders:
                    replacements.add("instance _root_." + name)
                    continue
                normal = old_text.removeprefix("_root_.")'''

def rewrite(data,migration):
 path=HERE/'reviewed-anonymous-instances.json'
 reviews=json.loads(path.read_text()) if path.exists() else []
 selected=[r for r in reviews if r['module']==data['module']]
 if not selected:return B.rewrite(data,migration)
 inventory=json.loads(gzip.open(HERE/'preparation/native-owners-full-before.json.gz','rt').read())
 native={(r['module'],r['kernel_name']):r for r in inventory['declarations']}
 verified=set();source=data['source'].encode()
 for row in selected:
  assert hashlib.sha256(source).hexdigest()==row['source_sha256']
  a,b=row['start'],row['stop'];assert source[a:b]==b'instance'
  lo=source.rfind(b'\n',0,a)+1;hi=source.find(b'\n',b);hi=len(source) if hi<0 else hi
  assert source[lo:hi].decode()==row['source_line']
  assert row['source_line'].lstrip().startswith('local instance :')
  assert (row['module'],row['old']) in native and not native[row['module'],row['old']]['is_private']
  refs=[r for r in data['refs'] if r['kind']=='binder' and r['name']==row['old'] and (r['start'],r['stop'])==(a,b)]
  assert len(refs)==1 and migration.target(refs[0])['new']==row['new']
  verified.add((data['module'],row['old'],a,b))
 code=inspect.getsource(K.rewrite);assert code.count(B.OLD)==1 and code.count(OLD)==1
 code=code.replace(B.OLD,B.NEW).replace(OLD,NEW)
 scope=dict(vars(K));scope['reviewed_anonymous_binders']=verified;exec(compile(code,'<OE-W1 individually reviewed instance binder>','exec'),scope)
 return scope['rewrite'](data,migration)
