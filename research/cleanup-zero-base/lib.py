import pickle,collections,json,re
def load(S):
    N=pickle.load(open(f'{S}/zero/N.pkl','rb'))
    # fold reassoc-generated
    for p in [p for p in N if p.endswith('_assoc') and p[:-6] in N]:
        b=p[:-6]; N[b]['gen']+=1; N[b]['vi']|=N[p]['vi']-{b}; del N[p]
    for d in N.values():
        d['ti']={q for q in d['ti'] if q in N}; d['vi']={q for q in d['vi'] if q in N}
    for p,d in N.items(): d['users']=set(); d['tusers']=set()
    for p,d in N.items():
        for q in d['ti']|d['vi']: N[q]['users'].add(p)
        for q in d['ti']: N[q]['tusers'].add(p)
    for p,d in N.items(): d['isdef']=d['kind'] in('def','struct','inst')
    return N
def sh(p): return p.replace('SerrePositivity.','').replace('GeneralSymmetricSpectrum.','')
def clos(N,p,key='users'):
    seen=set(); st=[p]
    while st:
        x=st.pop()
        for y in N[x][key]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
