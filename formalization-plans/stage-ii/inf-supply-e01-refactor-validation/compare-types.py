import json
from pathlib import Path
b=Path(__file__).resolve().parent
old=json.loads((b/'before.json').read_text()); new=json.loads((b/'after.json').read_text())
assert old['hash_algorithm']==new['hash_algorithm']=='normalized Expr DAG mixHash proof-irrelevant v3b (term-level, proof marker)'
assert old['name_map']==new['name_map']
# Check every retained declaration; separately expose generated auxiliary additions/removals.
a={r['name']:r for r in old['declarations']}; z={r['name']:r for r in new['declarations']}
public=lambda n: not any(x in n for x in ['._proof_', '._aux_', '.match_', '._match_'])
missing=[n for n in a if public(n) and n not in z]
changed=[dict(name=n,field=k,before=a[n][k],after=z[n][k]) for n in a.keys() & z.keys() if public(n) for k in ['type_hash','kind','attributes','axioms'] if a[n][k]!=z[n][k]]
result=dict(algorithm=old['hash_algorithm'],public_declarations=sum(public(n) for n in a),missing=missing,changed=changed,added=sorted(z.keys()-a.keys()),removed=sorted(a.keys()-z.keys()),body_changes=[n for n in a.keys() & z.keys() if a[n]['body_hash']!=z[n]['body_hash']],success=not missing and not changed)
(b/'type-comparison.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
assert result['success']
