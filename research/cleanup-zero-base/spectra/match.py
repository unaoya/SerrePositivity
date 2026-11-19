import json,sys,collections,re,pickle
S=sys.argv[1]
R={}
for l in open(f'{S}/zero2/decls.jsonl'):
    x=json.loads(l); R[x['name']]=x
def area(m):
    p=m.split('.'); return p[2] if p[1]=='Spectra' else 'CatEnriched' if p[2]=='Enriched' else 'AdjComparison'
def user(n):
    m=re.match(r'_private\.(?:.*?)\.0\.(.*)$',n); return m.group(1) if m else n
def gen(n):
    l=n.rsplit('.',1)[-1]; return l.startswith('_') or l.startswith('match_') or re.match(r'(eq_\d+|congr_simp|eq_def|sizeOf_spec|injEq|inj|noConfusion\w*|recOn|casesOn|rec|ctorIdx|below|brecOn|ext_iff|mk)$',l) is not None
src={n for n,x in R.items() if x['line']>0 and not gen(n)}
src-={n for n in src if n.endswith('_assoc') and n[:-6] in src}
usrc={user(n):n for n in src}
def parent(n):
    p=user(n)
    while p and p not in usrc: p=p.rsplit('.',1)[0] if '.' in p else ''
    return usrc.get(p)
node={n:(n if n in src else parent(user(n)[:-6] if n.endswith('_assoc') else user(n).rsplit('.',1)[0])) for n in R}
N={}
for n,x in R.items():
    p=node[n]
    if not p: continue
    d=N.setdefault(p,{'t':set(),'v':set(),'gen':0})
    if p==n: d['t']|=set(x['tdeps'])
    else: d['gen']+=1; d['v']|=set(x['tdeps'])
    d['v']|=set(x['vdeps'])
for p,d in N.items():
    x=R[p]; d['area']=area(x['module']); d['file']=x['module'].split('.')[-1]; d['lines']=x['endLine']-x['line']+1
    d['kind']='inst' if x['inst'] else 'thm' if x['kind']=='thm' else 'def'; d['type']=x['type']; d['doc']=x['doc']
    d['ti']={node[c] for c in d['t'] if node.get(c) and node[c]!=p}; d['vi']={node[c] for c in d['v'] if node.get(c) and node[c]!=p}
    d['et']={c for c in d['t'] if c not in node}; d['ev']={c for c in d['v'] if c not in node}
for d in N.values(): d['users']=set()
for p,d in N.items():
    for q in d['ti']|d['vi']: N[q]['users'].add(p)
pickle.dump(N,open(f'{S}/zero2/N.pkl','wb'))
A=collections.defaultdict(dict)
for p,d in N.items(): A[d['area']][p]=d
for a,M in A.items(): print(a,len(M),'lines',sum(d['lines'] for d in M.values()),dict(collections.Counter(d['kind'] for d in M.values())))
SS=A['SymmetricSpectrum']; G=A['General']
key=lambda p:(p.split('.',2)+['',''])[2] or p
gk={key(p):p for p in G}
REN=[('mappingSpace','mappingObject'),('MappingSpace','MappingObject')]
def cand(p):
    k=key(p)
    if k in gk: return gk[k],'same'
    k2=k
    for a,b in REN: k2=k2.replace(a,b)
    if k2 in gk: return gk[k2],'renamed'
    return None,None
SPEC=re.compile(r'PointedSimplicialSet|SSet|sphere|Sphere|SimplexCategory|Pointed|circle|Circle')
def sig(p,which):
    d=N[p]; loc={key(q) for q in d[which+'i'] if N[q]['area'] in('General','SymmetricSpectrum')}
    loc={re.sub('mappingSpace','mappingObject',re.sub('MappingSpace','MappingObject',x)) for x in loc}
    e={c for c in d['e'+which] if not SPEC.search(c)} | {key(q) for q in d[which+'i'] if N[q]['area'] not in('General','SymmetricSpectrum')}
    return loc,e
def jac(a,b): return len(a&b)/len(a|b) if a|b else 1.0
pairs=[]; un=[]
for p in SS:
    q,how=cand(p)
    if q:
        tl,te=sig(p,'t'); gl,ge=sig(q,'t'); vl,ve=sig(p,'v'); wl,we=sig(q,'v')
        pairs.append((p,q,how,jac(tl,gl),jac(te|tl,ge|gl),jac(vl|ve,wl|we)))
    else: un.append(p)
print('SS nodes',len(SS),'paired',len(pairs),dict(collections.Counter(x[2] for x in pairs)),'unpaired',len(un))
print(' paired lines SS',sum(N[x[0]]['lines'] for x in pairs),' counterpart lines General',sum(N[x[1]]['lines'] for x in pairs),' unpaired SS lines',sum(N[p]['lines'] for p in un))
b=collections.Counter()
for x in pairs:
    b[('stmt-locals same' if x[3]==1 else 'stmt-locals differ', 'proof sim>=0.6' if x[5]>=0.6 else 'proof differs')]+=1
print(b)
strong=[x for x in pairs if x[3]==1 and x[5]>=0.6]
print(' strong pairs',len(strong),'SS lines',sum(N[x[0]]['lines'] for x in strong), dict(collections.Counter(N[x[0]]['kind'] for x in strong)))
weak=[x for x in pairs if not(x[3]==1 and x[5]>=0.6)]
print(' weak examples',[(key(x[0]),round(x[3],2),round(x[5],2)) for x in weak[:15]])
uf=collections.Counter(); ul=collections.Counter()
for p in un: uf[N[p]['file']]+=1; ul[N[p]['file']]+=N[p]['lines']
print(' unpaired SS by file:',[(f,c,ul[f]) for f,c in uf.most_common(45)])
gp={x[1] for x in pairs}; gu=[p for p in G if p not in gp]
gf=collections.Counter(N[p]['file'] for p in gu)
print('General without SS counterpart',len(gu),'lines',sum(N[p]['lines'] for p in gu),gf.most_common(30))
json.dump({'pairs':pairs,'un':un,'gu':gu},open(f'{S}/zero2/match.json','w'))
