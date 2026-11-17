"""Retain B3 guards; register only individually source/native-authenticated edits."""
from pathlib import Path
import gzip,hashlib,inspect,json,re
import bulk_namespace as B
import klw1_namespace as K
HERE=Path(__file__).resolve().parent.parent
OLD='''                normal = old_text.removeprefix("_root_.")'''
NEW='''                if (module, ref["name"], a, b) in reviewed_qualified_binders:
                    replacements.add("_root_." + name)
                    continue
                if old_text == "instance" and (module, ref["name"], a, b) in reviewed_anonymous_binders:
                    replacements.add("instance _root_." + name)
                    continue
                normal = old_text.removeprefix("_root_.")'''

def rewrite(data,migration):
 path=HERE/'reviewed-anonymous-instances.json'
 reviews=json.loads(path.read_text()) if path.exists() else []
 selected=[r for r in reviews if r['module']==data['module']]
 qualified_path=HERE/'reviewed-qualified-binders.json'
 qualified=[r for r in json.loads(qualified_path.read_text()) if r['module']==data['module']] if qualified_path.exists() else []
 audit_path=HERE/'reviewed-audit-name-literals.json'
 audit_literals=[r for r in json.loads(audit_path.read_text()) if r['module']==data['module']] if audit_path.exists() else []
 root_path=HERE/'reviewed-global-root-spellings.json'
 root_records=[r for r in json.loads(root_path.read_text())['records'] if r['module']==data['module']] if root_path.exists() else []
 if not selected and not qualified and not audit_literals and not root_records:return B.rewrite(data,migration)
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
 verified_qualified=set()
 for row in qualified:
  assert hashlib.sha256(source).hexdigest()==row['source_sha256']
  a,b=row['start'],row['stop'];assert source[a:b].decode()==row['spelling'] and row['old'].endswith('.'+row['spelling'])
  assert (row['module'],row['old']) in native and not native[row['module'],row['old']]['is_private']
  refs=[r for r in data['refs'] if r['kind']=='binder' and r['name']==row['old'] and (r['start'],r['stop'])==(a,b)]
  assert len(refs)==1 and migration.target(refs[0])['new']==row['new']
  prefix=source[source.rfind(b'\n',0,a)+1:a].decode();assert re.fullmatch(r'\s*(?:def|theorem|lemma|abbrev|opaque)\s+',prefix)
  same=[r for r in data['refs'] if (r['start'],r['stop'])==(a,b)]
  assert all(r['kind']=='binder' and r['name']==row['old'] or r['kind']=='local' and not r['name'] and not r['module'] for r in same)
  verified_qualified.add((data['module'],row['old'],a,b))
 verified_audit_literals=[]
 wanted_audit_spans={(r['start'],r['stop']) for record in audit_literals for r in record['rows']}
 audit_refs={}
 for ref in data['refs']:
  span=(ref['start'],ref['stop'])
  if span in wanted_audit_spans:audit_refs.setdefault(span,[]).append(ref)
 for record in audit_literals:
  assert hashlib.sha256(source).hexdigest()==record['source_sha256']
  assert hashlib.sha256((HERE/'namespace-rewrite-map.json').read_bytes()).hexdigest()==record['plan_sha256']
  for row in record['rows']:
   a,b=row['start'],row['stop'];assert source[a:b].decode()==row['old']
   quote=row['quote'].encode();assert quote in [b'`',b'``'] and source[a-len(quote):a]==quote
   owner=row['observed_native_owner'];assert (owner,row['old']) in native and not native[owner,row['old']]['is_private']
   assert migration.public_symbols[row['old']]['new']==row['new']
   semantic=[r for r in audit_refs.get((a,b),[]) if r['name']==row['old']]
   if quote==b'``':
    # Resolved Name quotations already use the original semantic rewrite.
    assert semantic and any((migration.target(r) or {}).get('new')==row['new'] for r in semantic)
   else:
    # A raw single-backtick Name literal is registry data, not a constant reference.
    assert not semantic
    verified_audit_literals.append((a,b,row['new']))
 verified_global_root_edits=[]
 wanted_root_spans={(row['start'],row['stop']) for record in root_records for row in record['rows']}
 root_refs={};root_commands={}
 for ref in data['refs']:
  span=(ref['start'],ref['stop'])
  if span in wanted_root_spans:root_refs.setdefault(span,[]).append(ref)
 for cmd in data['commands']:
  span=(cmd.get('start'),cmd.get('stop'))
  if span in wanted_root_spans:root_commands.setdefault(span,[]).append(cmd)
 for record in root_records:
  assert hashlib.sha256(source).hexdigest()==record['source_sha256']
  for row in record['rows']:
   a,b=row['start'],row['stop'];assert source[a:b].decode()==row['old']
   assert row['new']=='_root_.'+row['old'] and (row['old']=='HomotopicalAlgebra' or row['old'].startswith('HomotopicalAlgebra.'))
   if row['kind']=='open':
    candidates=[c for c in root_commands.get((a,b),[]) if c['kind']=='open' and c['mode'] in ['simple','local-simple'] and c['names']==[row['old']]]
    assert len(candidates)==1
   else:
    assert row['kind']=='term' and source[max(0,a-1):a]!=b'.'
    refs=root_refs.get((a,b),[]);assert refs and any(r['kind']=='term' for r in refs)
    assert all(r['name']==row['old'] and r['kind'] in ['term','syntax'] and migration.target(r) is None for r in refs)
    assert sorted({(r['module'],r['name'],r['kind']) for r in refs})==[tuple(x) for x in row['resolutions']]
   verified_global_root_edits.append((a,b,row['new']))
 code=inspect.getsource(K.rewrite);assert code.count(B.OLD)==1 and code.count(OLD)==1
 code=code.replace(B.OLD,B.NEW).replace(OLD,NEW)
 marker='''        for ref in candidates:
            # The command elaborator may also record a local at the position''';replacement='''        for ref in candidates:
            if ref["kind"] == "local" and not ref["name"] and not ref["module"] and (module, a, b) in reviewed_qualified_spans:
                continue
            # The command elaborator may also record a local at the position''';assert code.count(marker)==1;code=code.replace(marker,replacement)
 meta_marker="    # A qualified name in quoted or custom syntax can lack a semantic reference."
 assert code.count(meta_marker)==1
 code=code.replace(meta_marker,'    for a, b, name in reviewed_audit_name_literals + reviewed_global_root_edits:\n        edit({"start": a, "stop": b}, name)\n\n'+meta_marker)
 scope=dict(vars(K));scope['reviewed_audit_name_literals']=verified_audit_literals;scope['reviewed_global_root_edits']=verified_global_root_edits;scope['reviewed_anonymous_binders']=verified;scope['reviewed_qualified_binders']=verified_qualified;scope['reviewed_qualified_spans']={(m,a,b) for m,n,a,b in verified_qualified};exec(compile(code,'<OE-W1 individually reviewed instance binder>','exec'),scope)
 return scope['rewrite'](data,migration)
