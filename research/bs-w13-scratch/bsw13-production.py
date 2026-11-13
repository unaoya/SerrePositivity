from pathlib import Path

source = Path('/tmp/bsw13-tensor-probe.lean').read_text()
source = '\n'.join(line for line in source.splitlines() if not line.startswith('#print axioms'))+'\n'
source = source.replace('import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensor',
    'module\n\npublic import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal')
source = source.replace('\nimport ', '\npublic import ')
source = source.replace('noncomputable section', '''/-! # 完備導来テンソルの模型比較

## 概要
離散入力の完備導来テンソルを、導来頂点の自由解像度と有界上側の代数模型で比較する。
BS 著者版 Lemma 10.3 と Proposition 10.4 の間で使う。

## 方針
両模型に同じ自由解像度を指定し、導来完備化を同じ複体に適用する。

## 規約
次数はコホモロジー次数。代数の標準因子写像は解像度上の単位写像で比較する。

## 使われ方
BS 著者版 Remark 10.7 の係数環の比較。
-/

@[expose] public noncomputable section''')
source = source.replace('open CategoryTheory CategoryTheory.Limits SSet','namespace SerrePositivity.BhattScholze.Almost\n\nopen CategoryTheory CategoryTheory.Limits SSet')
source = source.replace('open SerrePositivity SerrePositivity.InfinityCategories SerrePositivity.DerivedCompletion',
    'open InfinityCategories DerivedCompletion')
source = source.replace('abbrev DVertex :=', '/-- 導来圏の半自由代表を指定する頂点。 -/\nabbrev DVertex :=')
source = source.replace('def completedModuleTensor (a : R) (X Y : DVertex R) : DVertex R :=', '''/-- 頂点の半自由複体のテンソルを導来 p 完備化して頂点に戻す。 -/
def completedModuleTensor (p : ℕ) (A : Type u) [CommRing A] (X Y : DVertex A) : DVertex A :=''')
source = source.replace('((derivedInfinityHomotopyEquivalence R).inverse.obj\n    ((derivedComplexCompletionFunctor R a).obj C)).pt',
    '((derivedInfinityHomotopyEquivalence A).inverse.obj\n    ((derivedComplexCompletionFunctor A (p : A)).obj C)).pt')
source = source.replace('def compareTensor (a : R)', 'def completedTensorAlgebraVertexIso (p : ℕ)')
i = source.index('def completedTensorAlgebraVertexIso')
j = source.index('def compareModuleTensor', i)
source = source[:i]+source[i:j].replace('R a S T','R (p : R) S T').replace(
    'completedModuleTensor R a','completedModuleTensor p R').replace(
    'derivedComplexCompletionFunctor R a','derivedComplexCompletionFunctor R (p : R)')+source[j:]
names = {
    'heartModel': 'moduleHeartProjectiveModel',
    'compareModuleTensor': 'completedTensorResolutionIso',
    'completedTensorLeft_comparison': 'completedTensorAlgebraLeft_resolution',
    'completedTensorRight_comparison': 'completedTensorAlgebraRight_resolution',
    'exists_heartUnitLift': 'exists_moduleHeartUnitLift',
}
for old, new in names.items():
    source = source.replace(old,new)
docs = {
    'def moduleHeartProjectiveModel': '離散頂点と同じ関手的自由解像度を有界上側の導来模型に指定する。',
    'def completedTensorAlgebraVertexIso': 'BS 著者版 Lemma 10.3 の完備代数テンソルの底を導来頂点で計算する。',
    'def completedTensorResolutionIso (': '有界上側の完備テンソルを二つの自由解像度のテンソルで計算する。',
    'theorem completedTensorResolutionIso_naturality': '自由解像度での計算は二つの加群の射に関して自然。',
    'lemma completedTensorAlgebraLeft_resolution': '完備代数テンソルへの左因子写像は、右因子の単位をテンソルして得られる。',
    'lemma completedTensorAlgebraRight_resolution': '完備代数テンソルへの右因子写像は、左因子の単位をテンソルして得られる。',
    'theorem exists_moduleHeartUnitLift': '代数の単位は次数零の単位複体から自由解像度への鎖写像で表せる。',
}
for needle, doc in docs.items():
    source = source.replace('private '+needle,needle)
    source = source.replace(needle, f'/-- {doc} -/\n'+needle)
source = source.replace('\n\n\n','\n\n')
Path('/tmp/BSW13CompletedModuleTensor.lean').write_text(source+'\nend SerrePositivity.BhattScholze.Almost\n')

source = Path('/tmp/bsw13-kernel-probe.lean').read_text().split('\n#print axioms perfectoidIdeal_radical')[0]
source = source.replace('import SerrePositivity.InfinityCategories.Derived.Homology',
    'import SerrePositivity.InfinityCategories.Derived.Homology\n'
    'import SerrePositivity.BhattScholze.Almost.CompletedModuleTensor')
source = 'module\n\n'+source
source = source.replace('\nimport ', '\npublic import ')
source = source.replace('noncomputable section', '''/-! # 商の perfectoid 化の核と複体の almost 零性

## 概要
BS 著者版 Proposition 10.4 と Lemma 10.5 の核とコホモロジーの条件を定める。
根基不変性と、離散加群に対する完備テンソルの消滅を示す。

## 方針
古典的な商の perfectoid 化の普遍性と、一般の perfectoid 商に対する Lemma 10.3 を使う。

## 規約
次数はコホモロジー次数。J-almost 零性は各コホモロジー加群の零化条件。

## 使われ方
BS 著者版 Proposition 10.4 の複体版。
-/

@[expose] public noncomputable section''')
source = source.replace('abbrev DVertex (A : Type u) [CommRing A] := (derivedInfinityCategory A) _⦋0⦌\n\n','')
docs = {
    'def quotientPerfdMap': '古典的な商の perfectoid 化への標準射（BS 著者版 Theorem 7.4）。',
    'def perfectoidKernel': 'BS 著者版 Definition 10.1 の perfectoid 化の核。',
    'theorem le_perfectoidKernel': '元のイデアルは perfectoid 化の核に含まれる。',
    'theorem perfectoidKernel_le': '元のイデアルを殺す perfectoid 環への写像は、この核も殺す。',
    'theorem perfectoidKernel_mono': 'perfectoid 化の核は元のイデアルについて単調。',
    'theorem perfectoidIdeal_radical': 'perfectoid 環の被約性により、核は元のイデアルの根基で決まる。',
    'def IsJAlmostZero': '全次数のコホモロジーが J-almost 零である（BS 著者版 Proposition 10.4）。',
    'def IsAlmostConnective': '正次数のコホモロジーが J-almost 零である（BS 著者版 Lemma 10.5）。',
    'theorem isAlmostZero_radical': '複体の J-almost 零性は根基で決まる。',
    'theorem quotientPerfdMap_surjective': '古典的な商への写像に対する BS 著者版 Theorem 7.4 の全射性。',
    'theorem perfectoidKernel_quotient_isIntegralPerfectoid': '核で割った商は古典的な perfectoid 化と環同型なので perfectoid。',
    'theorem perfectoidKernel_completedTensor_isZero_of_isAlmostZero':
        'BS 著者版 Proposition 10.4 の順方向を、任意の J と離散加群について示す。',
}
for needle, doc in docs.items():
    source = source.replace(needle, f'/-- {doc} -/\n'+needle)
Path('/tmp/BSW13AlmostConnectivity.lean').write_text(source+'\nend SerrePositivity.BhattScholze.Almost\n')
