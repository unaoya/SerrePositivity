import json,sys,collections,re,pickle
S=sys.argv[1]
R=[json.loads(l) for l in open(f'{S}/decls.jsonl')]
by={x['name']:x for x in R}
def user(n):
    m=re.match(r'_private\.(?:.*?)\.0\.(.*)$',n); return m.group(1) if m else n
def gen(n):
    l=n.rsplit('.',1)[-1]; return l.startswith('_') or l.startswith('match_') or re.match(r'(eq_\d+|congr_simp|eq_def|sizeOf_spec|injEq|inj|noConfusion\w*|recOn|casesOn|rec|ctorIdx|below|brecOn|ext_iff|mk)$',l) is not None
src={n for n,x in by.items() if x['line']>0 and not gen(n)}
usrc={user(n):n for n in src}
def parent(n):
    p=user(n)
    while p and p not in usrc:
        p=p.rsplit('.',1)[0] if '.' in p else ''
    return usrc.get(p)
# ctor/rec/projection fold into structure? keep projections; fold ctor & rec
node={}
for n,x in by.items():
    p = n if n in src and x['kind'] not in('ctor','rec') else parent(user(n).rsplit('.',1)[0] if '.' in n else '')
    node[n]=p
N={}; ORPH=[]
for n,x in by.items():
    p=node[n]
    if p is None: ORPH.append(n); continue
    d=N.setdefault(p,{'t':set(),'v':set(),'gen':0})
    if p==n: d['t']|=set(x['tdeps'])
    else: d['gen']+=1; d['v']|=set(x['tdeps'])
    d['v']|=set(x['vdeps'])
for p,d in N.items():
    d['ti']={node[c] for c in d['t'] if c in node and node[c] and node[c]!=p}
    d['vi']={node[c] for c in d['v'] if c in node and node[c] and node[c]!=p}-set()
    x=by[p]; d['area']=x['module'].split('.')[1]; d['kind']=('inst' if x['inst'] else 'thm' if x['prop'] and x['kind']=='thm' else 'thm' if x['kind']=='thm' else 'struct' if x['kind']=='inductive' else 'def')
    d['lines']=x['endLine']-x['line']+1; d['file']=x['module'].split('.')[-1]; d['doc']=x['doc']; d['type']=x['type']
    d['ext_t']={c for c in d['t'] if c not in node}; d['ext_v']={c for c in d['v'] if c not in node}
users=collections.defaultdict(set); tusers=collections.defaultdict(set)
for p,d in N.items():
    for q in d['ti']|d['vi']: users[q].add(p)
    for q in d['ti']: tusers[q].add(p)
for p,d in N.items(): d['users']=users[p]; d['tusers']=tusers[p]
# definition layers
defs={p for p,d in N.items() if d['kind'] in('def','struct','inst')}
layer={}
def L(p,seen=()):
    if p in layer: return layer[p]
    if p in seen: return 0
    deps=[q for q in (N[p]['ti']|N[p]['vi']) if q in defs]
    layer[p]=1+max([L(q,seen+(p,)) for q in deps],default=-1)
    return layer[p]
sys.setrecursionlimit(10000)
for p in defs: L(p)
for p,d in N.items():
    if p in defs: d['layer']=layer[p]
    else:
        ds=[q for q in d['ti'] if q in defs]
        d['about']=sorted(ds,key=lambda q:-layer[q])
        d['layer']=None
print('orphans',len(ORPH),[o for o in ORPH if 'eq_1' not in o and 'congr_simp' not in o][:10])
pickle.dump(N,open(f'{S}/N.pkl','wb'))
for area in ['Spectra','LengthAlgebra']:
    A={p:d for p,d in N.items() if d['area']==area}
    k=collections.Counter(d['kind'] for d in A.values())
    print('=====',area,len(A),dict(k),'gen folded',sum(d['gen'] for d in A.values()))
    print(' def layers',sorted(collections.Counter(d['layer'] for p,d in A.items() if p in defs).items()))
    th=[d for d in A.values() if d['kind']=='thm']
    print(' thm: about no local def',sum(1 for d in th if not d['about']),' lines total',sum(d['lines'] for d in th),' def lines',sum(d['lines'] for p,d in A.items() if p in defs))
    nouse=[p for p,d in A.items() if not d['users']]
    print(' no in-range user:',len(nouse),dict(collections.Counter(N[p]['kind'] for p in nouse)))
    one=[p for p,d in A.items() if len(d['users'])==1]
    print(' exactly one in-range user:',len(one),dict(collections.Counter(N[p]['kind'] for p in one)))
    ty=collections.defaultdict(list)
    for p,d in A.items(): ty[re.sub(r'\s+',' ',d['type'])].append(p)
    dup=[v for v in ty.values() if len(v)>1]
    print(' identical statement groups:',len(dup),[ [x.split('.')[-1] for x in v] for v in dup][:8])
    ld=collections.Counter()
    for d in A.values(): ld['thm<=3' if d['kind']=='thm' and d['lines']<=3 else d['kind']]+=1
    print(' lines hist thm:',sorted(collections.Counter(min(d['lines']//10*10,60) for d in th).items()))
