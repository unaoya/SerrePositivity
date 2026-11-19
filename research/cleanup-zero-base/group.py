import sys,collections,json,pickle; S=sys.argv[1]; sys.path.insert(0,S+'/zero'); from lib import *
N=load(S)
ext=json.load(open(f'{S}/zero/ext.json'))
HUB={'Spectra':[
 ('スペクトルの定義と構造射',['GeneralSymmetricSpectrum']),
 ('極限・余極限',['limitLevelIso','colimitLevelIso','forget_createsLimits','forget_createsColimitsOfShape']),
 ('自由スペクトルと評価',['freeFunctor','freeObj','freeAt','evaluation']),
 ('自由スペクトルの各段の表示',['freeAtLevelDiagram','freeAtLevelInductionDiagram','freeAtLevelBlockQuotient','freeAtLevelInductionAction','freeAtLevelInductionActionFunctor']),
 ('テンソル積と内部 Hom',['tensor','internalHom']),
 ('基礎圏の作用（テンソル）',['pointwiseTensor','pointwiseTensorFunctor']),
 ('余テンソル',['cotensor','homBySequenceCotensorIso']),
 ('写像対象',['mappingObjectFunctor','mappingObject']),
 ('豊穣（合成・単位・表現可能性）',['mappingObjectComposition','mappingObjectUnit','mappingObjectArrow','mappingObjectEvaluation','tensorMappingParameterIso','cotensorMappingParameterIso','tensorMappingPowerAdjunction','cotensorMappingAdjunction']),
 ('懸垂の構造射とシフト',['suspensionMap','adjointStructureMap','shiftedHom','shiftedHomStructureIndex']),
 ('単体集合の場合とシリンダー',['simplicialParameterFunctor','intervalBoundaryTensorMap','simplicialCotensorNatIso'])],
 'LengthAlgebra':[
 ('正規化長さ',['NormalizedLength']),
 ('係数の制限と上限',['NormalizedLength.comap','NormalizedLength.HasSup','NormalizedLength.restrict']),
 ('零長さの Serre 類と商',['LengthAlgebra.finiteLengthTorsion','LengthAlgebra.torsionLength']),
 ('完全複体の Euler 評価',['LengthAlgebra.perfectModuleHomology','LengthAlgebra.perfectFiniteHomology','LengthAlgebra.koszulScalars','LengthAlgebra.ordinaryBaseEulerK0']),
 ('Koszul の有限性と Euler',['LengthAlgebra.KoszulFinite','LengthAlgebra.koszulEuler','koszulModuleAlgebraHomologyIso']),
 ('根の塔：段と三段階の長さ',['Section2.presentedLength','Section2.stageToStage','Section2.stageToTower']),
 ('根の塔：基底変更',['Section2.TS','Section2.TSj']),
 ('根の塔：加法性と塔の長さ',['RootTowerLength.normalizedLength']),
 ('根の塔：完備と座標',['RootTowerLength.completedStageModule','RootTowerLength.completedQuotientStageModule','RootTowerLength.coordinateQuotientIdeal','RootTowerLength.coordinateZeroExponent'])]}
def find(area,s):
    c=[p for p,d in N.items() if d['area']==area and (sh(p)==s or p.split('.')[-1]==s)]
    assert len(c)==1,(s,c); return c[0]
G={}
deps=lambda p:N[p]['ti']|N[p]['vi']
for area,hs in HUB.items():
    hub={}
    for i,(lab,names) in enumerate(hs):
        for s in names: hub[find(area,s)]=i
    memo={}
    sys.setrecursionlimit(100000)
    def tr(p,stack=()):
        if p in memo: return memo[p]
        s=set()
        if p in hub: s.add(hub[p])
        if p not in stack:
            for q in deps(p): s|=tr(q,stack+(p,))
        memo[p]=s; return s
    for p,d in N.items():
        if d['area']!=area: continue
        s=tr(p); d['hubs']=s; d['g']=max(s) if s else -1
    G[area]=hs
pickle.dump((N,HUB),open(f'{S}/zero/G.pkl','wb'))
for area,hs in HUB.items():
    A={p:d for p,d in N.items() if d['area']==area}
    print('=====',area,len(A))
    for i,(lab,_) in list(enumerate(hs))+[(-1,('（範囲の定義に頼らない）',0))]:
        M={p:d for p,d in A.items() if d['g']==i}
        if not M: continue
        files=collections.Counter(d['file'] for d in M.values())
        below=collections.Counter()
        for d in M.values():
            for q in d['ti']|d['vi']:
                if N[q]['g']!=i: below[N[q]['g']]+=1
        k=collections.Counter(d['kind'] for d in M.values())
        print(f"[{i}] {lab}: {len(M)} (def {k['def']+k['struct']}, inst {k['inst']}, thm {k['thm']}) lines {sum(d['lines'] for d in M.values())} | files {len(files)} | uses groups {sorted(below)}")
        print('     files:',dict(files.most_common(8)))
    # file purity
    fg=collections.defaultdict(collections.Counter)
    for p,d in A.items(): fg[d['file']][d['g']]+=1
    mixed={f:dict(c) for f,c in fg.items() if len(c)>1}
    print(' files total',len(fg),'mixed',len(mixed))
    for f,c in mixed.items(): print('    ',f,c)
# the 42
th=[p for p,d in N.items() if d['area']=='LengthAlgebra' and d['g']==-1]
c=collections.Counter()
for p in th:
    d=N[p]; e=[x for x in d['ext_t'] if x.startswith('SerrePositivity')]
    c['uses outside SerrePositivity defs in statement' if e else 'Mathlib only']+=1
print(c)
print([sh(p) for p in th if not [x for x in N[p]['ext_t'] if x.startswith('SerrePositivity')]][:40])
