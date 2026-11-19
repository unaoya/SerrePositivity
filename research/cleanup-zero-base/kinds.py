import sys,json,pickle,collections,re,subprocess
S=sys.argv[1]; sys.path.insert(0,S+'/zero')
N=pickle.load(open(f'{S}/zero2/N.pkl','rb'))            # General, SS, CatEnriched, AdjComparison
import lib; L=lib.load(S)                                  # LengthAlgebra (+General dup)
for p,d in L.items():
    if d['area']=='LengthAlgebra':
        d2=dict(d); N[p]=d2
R={}
for f in ['zero/decls.jsonl','zero2/decls.jsonl']:
    for l in open(f'{S}/{f}'):
        x=json.loads(l); R[x['name']]=x
def user(n):
    m=re.match(r'_private\.(?:.*?)\.0\.(.*)$',n); return m.group(1) if m else n
def owner(c):
    p=c
    while p and p not in N:
        u=user(p); p=u.rsplit('.',1)[0] if '.' in u else ''
        if u!=p and u in N: return u
    return p or None
ext=collections.defaultdict(set); extmod=collections.defaultdict(set)
for l in open(f'{S}/zero/users.jsonl'):
    x=json.loads(l); u=re.sub(r'\.(_proof_\d+(_\d+)?|_simp_\d+(_\d+)?|eq_\d+|match_\d+(_\d+)?)$','',user(x['user']))
    for c in set(x['t'])|set(x['v']):
        o=owner(c)
        if o: ext[o].add(u); extmod[o].add('.'.join(x['module'].split('.')[1:3]))
# cross-area users inside target set
for p,d in N.items():
    d['xusers']={q for q in d['users'] if N[q]['area']!=d['area']} if all(q in N for q in d['users']) else set()
# table-named (short name, noisy)
names=sorted({p.split('.')[-1] for p in N})
open(f'{S}/zero/allnames.txt','w').write('\n'.join(names)+'\n')
out=subprocess.run(f"rg -F -w -o -f {S}/zero/allnames.txt research -g '*-coverage/**/*.csv' --no-filename | sort | uniq -c",shell=True,capture_output=True,text=True).stdout
tab=collections.Counter()
for l in out.splitlines():
    k,n=l.split(None,1); tab[n.strip()]=int(k)
src={}
def body(p):
    x=R[p]; f=x['module'].replace('.','/')+'.lean'
    if f not in src: src[f]=open(f).read().split('\n')
    return '\n'.join(src[f][x['line']-1:x['endLine']])
def kind(p):
    d=N[p]; b=body(p); tail=b.split(':=')[-1].strip() if ':=' in b else ''
    para = (d['kind']=='thm' and (re.fullmatch(r'(by\s+)?rfl',tail) or ('\n' not in tail and len(tail)<200 and not tail.startswith('by')))) or (d['kind']!='thm' and '\n' not in tail and len(tail)<200 and 'where' not in b and tail!='')
    nin=len(d['users']); nex=len(ext[p]); named=tab[p.split('.')[-1]]>0 and len(p.split('.')[-1])>=10
    tot=nin+nex
    if tot==0 and not named: k='未使用'
    elif para: k='言い換え'
    elif named or nex>0 or d.get('xusers'): k='結果'
    elif tot>=2: k='再利用される補題'
    else: k='分割のための補題'
    d['K']=k; d['nex']=nex; d['named']=named; return k
for p in N: kind(p)
pickle.dump((N,{k:sorted(v) for k,v in ext.items()}),open(f'{S}/zero/K.pkl','wb'))
for a in ['LengthAlgebra','General','SymmetricSpectrum','CatEnriched','AdjComparison']:
    M={p:d for p,d in N.items() if d['area']==a}
    c=collections.Counter(d['K'] for d in M.values()); ln=collections.Counter()
    for d in M.values(): ln[d['K']]+=d['lines']
    print('==',a,len(M),sum(ln.values()))
    for k in ['結果','再利用される補題','分割のための補題','言い換え','未使用']: print(f'   {k}: {c[k]} 件 {ln[k]} 行')
    em=collections.Counter()
    for p in M:
        for m in extmod[p]: em[m]+=1
    print('   used from:',em.most_common(8))
    print('   para kept by usage: 言い換え with ext users',sum(1 for d in M.values() if d['K']=='言い換え' and d['nex']>0),' 言い換え unused',sum(1 for d in M.values() if d['K']=='言い換え' and len(d['users'])+d['nex']==0))
