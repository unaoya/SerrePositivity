# P⁰のためのP1〜P3：段0（紙、⑤d、2026-11-16）

基準main：`79c1315e7`。枝：`codex/p0-p1-p3-stage0`。
[p0-plan-draft.md](/Users/sugakubunka/Documents/LEAN_Projects.nosync/SerrePositivity/formalization-plans/stage-ii/p0/p0-plan-draft.md)とD81、ユーザー方針11-16に従う。
Leanの追加・変更・移動・ビルドはしない。以下は主出力の**候補一覧30項目**であり、実装・外枠の承認ではない。
打ち切ったG12のモナド経路は再開しない。M15も停止を維持する。

## 0. 判断材料

D(k)の安定・presentableと、通常の複体のtensor・projective模型は実在する。
不足はN(Fin_*)上の全operadic構造と、その同じD(k)への多入力の局所化・比較である。
P⁰の定義に必要な範囲でも、Σ_p作用をh圏の等式にしたり、CAlgをBEの局所化で定義したりして縮めない。

選んだD(k)先行経路のM（最小の出力とその構成に使う周辺）25項目は、
素 **29,200〜56,900行**、係数2の補正後 **58,400〜113,800行**。
CAlg内のtensor＝余積・一般の相対tensorまで含めるEの4項目は、別に **13,800〜27,200行**（補正後）。
Mod_Hk≃D(k)の比較Cの1項目は、Sp等の基盤供給後に **7,000〜16,000行**（補正後）。
30項目全ての和は補正後 **79,200〜157,000行**。これはSpの新造・P4〜P6・整流・HA全書の費用を含まない。
従ってこの値をP⁰完成の総量や実装外枠として使わない。

## 1. 対応表を一件ずつ分けた範囲

p0-mapのP1〜P3に直接対応するnone/partialは9件。
一覧と各件の採否・不足を [p0-items.csv](p1-p3-stage0/p0-items.csv) に置く。
HAのreviewから次の範囲の各行を取り、**326件（none 270・partial 56）**を
[ha-items.csv](p1-p3-stage0/ha-items.csv) に記録した。

- 2.0、2.1、2.2.1、2.4：Fin_*、∞-operad、maps、monoidal、Cartesian/余Cartesian、局所化の周辺。
- 3.2.2〜3.2.4、3.3.1・3.3.3：CAlg、極限・余極限、モノイダル構造、固定moduleの定義。
- 4.1.7、4.2.1、4.5：モノイダル局所化、LM/RM、可換代数上の加群。
- 7.1.2、7.2.4：複体の模型、D(k)との比較、perfectとcompact。

CSVは各番号の既存宣言・型差の理由を保ち、最小M／拡張E／条件つきC／全体化Fへ個別に対応させた。
各番号を独立の新しい定理として数え直さず、同じ構成の法則は下の主出力にまとめる。
各CSV行の見積もりは対応するIDの見積もりへの参照であり、全行を加算して二重計上しない。
reviewのnone/partialを変更しておらず、今回の紙によって新たにown・完成へ上げた行はない。
reviewの既存宣言があるファイルの現存は照合したが、過去のkernel監査は再実行していない。
原典本文を照合した中心番号と、既存reviewの型差を再分類した周辺行を区別する。
326件を原典の全証明まで再監査したという報告ではない。

p0-mapにはD75に基づく古い説明が残るが、CAlgの方針はD81で読む。
また4.5.2.1は現在のHAでは**Theorem**であり、地図の「構成」は種別の記録として訂正候補。
3.2.4.7のpartialは通常CommAlgCat、4.5.2.1は通常balanced tensor、7.2.4.2はdgの通常compactの部分である。
これらをHAのnativeな結論の完成と数えない。

## 2. 原典と型の共通規約

- [HA（2017-09-18）](https://www.math.ias.edu/~lurie/papers/HA.pdf)：2.0.0.7、2.1.1.10、2.1.3.1、
  2.4、3.2.4.7、4.1.7.4–6、4.5.2.1、7.1.2.8・11–13、7.2.4.2を中心に本文を照合。
- [DAG XIII](https://www.math.ias.edu/~lurie/papers/DAG-XIII.pdf)：Construction 2.2.1–2、Remark 2.2.4、Example 2.2.5、Construction 2.2.6。
- Kerodon [§5.6、Tag 027M](https://kerodon.net/tag/027M)：分類と相対関手、
  [§5.3.1.10、Tag 02T1](https://kerodon.net/tag/02T1)：cocartesian切断の型の土台。
  分類の全関手・写像空間・fiberの比較は既存実装を再利用し、構成し直す見込みには入れない。
- [Nikolaus–Scholze](https://arxiv.org/pdf/1707.01799)：I.3のlax対称モノイダルなTateはP4との境界。
  Sp上の原典の結果をD(k)へそのまま代入できるとはしない。

以下は**紙上のLean風の仕様**。未定義名は新設候補で、コンパイル済みの型ではない。
`FunInfinity K C`は内部Homによる全関手準圏、`FunctorHom`はその実自然変換、
`FunctorIso`・`QCatEquivalence`は既存のnativeな全比較を表す。
`fiber`は指定頂点での全fiber、`Vertex C`はCの零単体。
小さい形状はSSet.{u}、D(k)等はSSet.{u+1}、Cat∞で分類するときは必要な宇宙をもう一つ上げる。
その大小・fiberの本質的小ささも検収対象とし、同じD(k)の宇宙を変更して完成としない。
P3のtensorLeft/right等は、明示したfiberOneの同値に沿って既存D(k)へ移した関手の略記である。

`IsInfinityOperad p`の三条件は、準圏Oとpの下で、全inert射のp-cocartesian lift、
全fの写像空間の`Map_f(x,y) → ∏_i Map_(ρ_i∘f)(x,y_i)`の同値、全色列の持上げ。
全辺でのcocartesian liftは要求しない。対称モノイダルの場合に全辺でのliftと全arityのSegalを証明する。
「最小」は使う定理の範囲を指し、∞-operadの定義をarity≤pで切り詰める意味ではない。

配置は以下の`InfinityCategories/HA/`からの相対節名。実際の新設時には既存のHAレイアウトの綴りへ揃え、
対応する`@[cite HA "番号"]`・`@[kerodon TAG]`を付ける。型の弱い成分にはpartialの種類と型差を残す。

## 3. 型つき初期一覧・既存の土台・配置

M＝選択した最小経路の構成に使用、E＝強い周辺の拡張、C＝外部のSp基盤待ちの比較。
全30項目とも新しい実装は未着手。下の費用は既存コードを含まない追加Lean行数。

### P1-01　Fin_*の骨格・標準慣性射（M）

原典：2.0.0.2–5; 2.1.1.8–9。素 700–1,200行、×2 **1,400–2,400行**。

```lean
FinStar : Type
Category FinStar
finStarNerve : SSet
rho (n : ℕ) (i : Fin n) : pointedFin (n+1) ⟶ pointedFin 2
finitePointedEquivalence : FinStar ≌ FinitePointedSets
```

土台・乗せ方：MathlibのPointed・FintypeCat・Fin・有限写像。Optionの基点付加だけではFin_*の骨格・ρ_i・全fiberの指定は未供給。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/FinitePointedSets/`。

### P1-02　active・inertと標準分解（M）

原典：2.1.2.1–6。素 500–900行、×2 **1,000–1,800行**。

```lean
IsInert, IsActive : (a b : FinStar) → (a ⟶ b) → Prop
∀ f, ∃ i a, IsInert i ∧ IsActive a ∧ i ≫ a = f
-- 分解の選択の可縮性・合成との両立も構成する。
```

土台・乗せ方：P1-01の有限写像の実fiberで構成する。通常のmono/epi分解をそのままinert/activeとしない。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/ActiveInert/`。

### P1-03　∞-operadの三条件とComm（M）

原典：2.1.1.10–18。素 1,000–1,800行、×2 **2,000–3,600行**。

```lean
IsInfinityOperad (p : O ⟶ nerve FinStar) : Prop
-- Oは準圏。全inert lift、Map_fの有限積分解、全色列の持上げの三条件。
commInfinityOperad : IsInfinityOperad (𝟙 (nerve FinStar))
```

土台・乗せ方：KerodonのCocartesianFibration・pinched mapping space・有限積・実fiberを利用。pの全辺のliftは要求せず、inert liftの三条件を原典どおり定義する。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/InfinityOperads/`。

### P1-04　operad写像・相対関手準圏（M）

原典：2.1.2.7–12; 2.1.3.7–8。素 700–1,200行、×2 **1,400–2,400行**。

```lean
OperadMapSpace (O P : InfinityOperad) : SSet
Quasicategory (OperadMapSpace O P)
-- 底上の実関手でinert辺を保つものが張る全部分関手準圏。
```

土台・乗せ方：InnerFibrations/RelativeFunctor.leanの全部分相対関手準圏を拡張。全cocartesian辺の保存を要求する既存型から、inertだけの保存を分ける。2.1.3.8のleft fibration限定の比較も一般化が残る。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/Maps/`。

### P1-05　対称モノイダル∞圏の定義・Segal（M）

原典：2.0.0.7; 2.1.2.13–20。素 1,000–1,800行、×2 **2,000–3,600行**。

```lean
structure SymmetricMonoidalInfinityCategory where
  total : SSet
  projection : total ⟶ nerve FinStar
  cocartesian : CocartesianFibration projection
  segal : ∀ n, IsQCatEquivalence (inertFiberComparison projection n)
-- n=0のfiberは終準圏と比較する。
```

土台・乗せ方：既存の余Cartesian fibration、全fiber間の移送と積準圏。二項tensor・結合子だけを定義としない。全nのinert比較が同値であることが構造の本体。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/SymmetricMonoidal/`。

### P1-06　O-monoidal構造と多入力移送（M）

原典：2.1.2.13–17。素 700–1,300行、×2 **1,400–2,600行**。

```lean
OMonoidalInfinityCategory (O : InfinityOperad) : Type
operationFunctor (M : OMonoidalInfinityCategory O) (α : Mul O xs y) :
  productCategory (fun i => M.fiber (xs i)) ⟶ M.fiber y
-- 全底変換・慣性分解・合成に適合。
```

土台・乗せ方：P1-03〜05の底変換・色のfiberとKerodonの相対移送。色の列を積で表し実多入力関手と全合成を回収。P1-05と共通法則は二重計上しない。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/OMonoidal/`。

### P1-07　通常の対称モノイダル圏のnerve（M）

原典：2.0.0.1–7; 2.1.1.7,21; 2.1.2.21。素 1,500–2,800行、×2 **3,000–5,600行**。

```lean
monoidalNerve (C : Type) [Category C] [MonoidalCategory C]
  [SymmetricCategory C] : SymmetricMonoidalInfinityCategory
QCatEquivalence (monoidalNerve C).fiberOne (nerve C)
-- sourceは有限列と各fiberのtensorから作る実作用素圏。
```

土台・乗せ方：通常の対称モノイダル圏とnerve、有限列と全fiberのtensorから作用素圏を作る。一般のsimplicial colored operadからのnerveの全理論はF1へ分ける。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/MonoidalNerve/`。

### P1-08　Cartesian構造・Cat∞の可換代数との比較（M）

原典：2.4.1.1–9; 2.4.2.1–7。素 1,500–2,800行、×2 **3,000–5,600行**。

```lean
cartesianMonoidal (C : SSet) [Quasicategory C] (h : HasFiniteProducts C) :
  SymmetricMonoidalInfinityCategory
QCatEquivalence (cartesianMonoidal C h).fiberOne C
OMonoidalObjects CatInfinity O ≃ OMonoidalInfinityCategories O
-- 最後は∞圏の同値として構成し、集合の全単射へ切り詰めない。
```

土台・乗せ方：KerodonのCatInfinityと分類、有限積の普遍性。HA 2.4.2.6のCat∞の可換代数というDAGの表示、および4.1.7の原典の構成を追うための選択。全一般化operadの弱近似はF3。

配置：`InfinityCategories/HA/InfinityOperads/ProductsAndCoproducts/Cartesian/`。

### P1-09　余Cartesian構造と有限余積の判定（E）

原典：2.4.3.1–12,17–19。素 1,200–2,400行、×2 **2,400–4,800行**。

```lean
cocartesianMonoidal (C : SSet) [Quasicategory C] (h : HasFiniteCoproducts C) :
  SymmetricMonoidalInfinityCategory
IsCocartesianMonoidal M ↔ UnitIsInitial M ∧ TensorIsCoproduct M
```

土台・乗せ方：有限余積の既存native錐、P1-05の操作。後のP2-07のCAlg内での普遍性に使用。任意一般化operadの族の比較は含めない。

配置：`InfinityCategories/HA/InfinityOperads/ProductsAndCoproducts/Cocartesian/`。

### P1-10　分類関手とのSegal・fiberの比較（M）

原典：2.1.2.17–19; 2.4.2.4,6–7。素 700–1,400行、×2 **1,400–2,800行**。

```lean
classifiedSegalComparison (χ : nerve FinStar ⟶ CatInfinity) :
  (IsSegalDiagram χ ↔ IsSegalCocartesianFamily (unstraighten χ))
-- χを実際に作った後に適用する定理。任意χがSegalとは仮定しない。
```

土台・乗せ方：Kerodon 5.6の分類とfiber/transportの比較。分類の存在だけではSegalは出ず、実χの全inert成分を証明する。小ささとu+1/u+2の上昇も検収。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/ClassifiedSegal/`。

### P2-01　Alg_O・CAlgの実準圏（M）

原典：2.1.3.1–4。素 1,400–2,600行、×2 **2,800–5,200行**。

```lean
AlgInfinity (C O P : InfinityOperad)
  (q : OperadicFibration C O) (α : OperadMap P O) : SSet
Quasicategory (AlgInfinity C O P q α)
CAlgInfinity (M : SymmetricMonoidalInfinityCategory) : SSet
-- Algはq∘s=αを満たすinert保存切断の全部分相対関手準圏。
```

土台・乗せ方：P1-04のinert保存相対関手準圏、全切断。3.2の結果やBEの局所化をCAlgの定義の欄へ入れない。準圏性・評価と全自然変換まで構成する。

配置：`InfinityCategories/HA/InfinityOperads/Foundations/AlgebraObjects/`。

### P2-02　評価・忘却・写像への自然性（M）

原典：2.1.3.1,4,7–8; 3.2.2.6。素 700–1,300行、×2 **1,400–2,600行**。

```lean
cAlgForget M : CAlgInfinity M ⟶ M.fiberOne
cAlgMap (F : LaxSymmetricMonoidalFunctor M N) : CAlgInfinity M ⟶ CAlgInfinity N
FunctorIso (cAlgMap F ≫ cAlgForget N) (cAlgForget M ≫ F.underlying)
IsConservative (cAlgForget M)
```

土台・乗せ方：P2-01からの評価と実前合成。cAlgForgetDerivedは別模型の入力なのでこの証明へ無条件に代入しない。

配置：`InfinityCategories/HA/AlgebrasAndModulesOverInfinityOperads/Algebras/Functoriality/`。

### P2-03　拡大冪・全Σ_n等変性（M）

原典：DAG XIII 2.2.1; 2.4.2.6。素 1,000–2,000行、×2 **2,000–4,000行**。

```lean
extendedPowerFunctor (M : SymmetricMonoidalInfinityCategory) (n : ℕ) :
  M.fiberOne ⟶ FunInfinity (BG (Equiv.Perm (Fin n))) M.fiberOne
FunctorIso (extendedPowerFunctor M n ≫ evaluationBasepoint) (tensorPower M n)
-- C^(n)=(C^n×EΣ_n)/Σ_nからの構成との全比較。
```

土台・乗せ方：P1-05の⟨n⟩の自己同型とactive ⟨n⟩→⟨1⟩の全輸送、またはP1-08のCAlg(Cat∞)表示。既存tensorPowerRepresentationFunctorとの比較はP3-04で行う。

配置：`InfinityCategories/HA/InfinityOperads/ProductsAndCoproducts/ExtendedPowers/`。

### P2-04　乗法のΣ_n等変な全自然変換（M）

原典：DAG XIII 2.2.4; 2.1.3.1。素 800–1,600行、×2 **1,600–3,200行**。

```lean
equivariantMultiplication (M : SymmetricMonoidalInfinityCategory) (n : ℕ) :
  FunctorHom (cAlgForget M ≫ extendedPowerFunctor M n)
    (cAlgForget M ≫ trivialActionFunctor (Equiv.Perm (Fin n)))
-- 全BΣ_n上の自然変換。各σのh圏での等式だけではない。
```

土台・乗せ方：可換代数の全inert保存切断がactive collapseと全置換を同時に与えることから構成。n個のσについての個別等式を足すだけでは全BΣ_nの自然変換にならない。

配置：`InfinityCategories/HA/AlgebrasAndModulesOverInfinityOperads/Algebras/EquivariantMultiplication/`。

### P2-05　homotopy orbit冪・μの因子化（M）

原典：DAG XIII 2.2.1,4; 3.2.3.1–2。素 1,200–2,400行、×2 **2,400–4,800行**。

```lean
symmetricPower M n (h : HasBGColimits M.fiberOne) : M.fiberOne ⟶ M.fiberOne
-- Sym^n(X)=colim_(BΣ_n) X^(⊗n)、元の指定余錐も保持。
symmetricPowerMultiplication :
  FunctorHom (cAlgForget M ≫ symmetricPower M n h) (cAlgForget M)
-- G→Σ_nの制限からorbit_G→orbit_Σ_nへの全比較。
```

土台・乗せ方：Kerodonの全Kan延長・余極限、D(k)のpresentability。BGは群が有限でも一般に有限単体集合ではない。普通のcoinvariantsをhomotopy orbitと同一視しない。

配置：`InfinityCategories/HA/AlgebrasAndModulesOverInfinityOperads/LimitsAndColimits/SymmetricPowers/`。

### P2-06　CAlgの点ごとの対称モノイダル構造（E）

原典：3.2.4.1–5。素 1,700–3,200行、×2 **3,400–6,400行**。

```lean
cAlgMonoidal M : SymmetricMonoidalInfinityCategory
QCatEquivalence (cAlgMonoidal M).fiberOne (CAlgInfinity M)
cAlgForgetMonoidal M : SymmetricMonoidalFunctor (cAlgMonoidal M) M
```

土台・乗せ方：P2-01と全入力に関するinert保存。一般の代数のモノイダル構造の必要なCAlgの場合。通常CommAlgCatのMonoidalCategoryを∞の定義に代用しない。

配置：`InfinityCategories/HA/AlgebrasAndModulesOverInfinityOperads/LimitsAndColimits/MonoidalStructure/`。

### P2-07　CAlgのtensor＝余積とCAlg内の等変乗法（E）

原典：3.2.4.7–8。素 1,800–3,500行、×2 **3,600–7,000行**。

```lean
IsCocartesianMonoidal (cAlgMonoidal M)
-- 全CAlg内での有限余積錐とtensorの同じ脚の比較。
equivariantCAlgFold M n : FunctorHom
  (extendedPowerFunctor (cAlgMonoidal M) n)
  (trivialActionFunctor (Equiv.Perm (Fin n)))
```

土台・乗せ方：P1-09の余Cartesian判定とP2-06。指定したtensor脚と余積脚の全比較、CAlg内のfoldを構成する。最小のC内の乗法P2-04より強い。

配置：`InfinityCategories/HA/AlgebrasAndModulesOverInfinityOperads/LimitsAndColimits/CoproductTensor/`。

### P2-08　lax関手から代数・加群の像（M）

原典：2.1.2.7; 2.1.3.1; 4.5.1.1。素 700–1,400行、×2 **1,400–2,800行**。

```lean
mapModule (F : LaxSymmetricMonoidalFunctor M N) (A : CAlgInfinity M) :
  ModuleInfinity M A ⟶ ModuleInfinity N (cAlgMap F A)
FunctorIso (mapModule F A ≫ moduleForget _) (moduleForget A ≫ F.underlying)
-- 乗法・単位・結合の全operadic coherenceを保持。
```

土台・乗せ方：P1-04のoperad写像、P2-09の加群の全定義。Tate自体のlax構造は⑤aのP4の別出力。単なる二項pairingからcoherent moduleを仮定しない。

配置：`InfinityCategories/HA/AlgebrasAndModulesOverInfinityOperads/Algebras/LaxFunctorImages/`。

### P2-09　固定可換代数のoperadic加群（M）

原典：3.3.1.1–12・3.3.3.1–17; 4.2.1.1–22,36–37; 4.5.1.1–6。素 4,000–8,000行、×2 **8,000–16,000行**。

```lean
comm_isCoherent : IsCoherentInfinityOperad commInfinityOperad
ModuleInfinity (M : SymmetricMonoidalInfinityCategory) (A : CAlgInfinity M) : SSet
Quasicategory (ModuleInfinity M A)
moduleForget A : ModuleInfinity M A ⟶ M.fiberOne
-- 固定Aの可換operadic moduleと必要な左module表示との比較。
```

土台・乗せ方：HA 3.3.1.12のCommのcoherenceを実証し（Extの有限集合と押し出し）、3.3.3のnull射からの相対Alg、LM/RMと固定可換代数のmodule。既存dg moduleの圏をHAの定義そのものとしない。一般pseudo-enrichmentや可変底の全理論はF6へ分ける。

配置：`InfinityCategories/HA/LeftAndRightModules/ModulesOverCommutativeAlgebras/Definition/`。

### P2-10　巡回群への制限と単位の自明作用（M）

原典：DAG XIII 2.2.1–2; 2.1.2.16。素 400–800行、×2 **800–1,600行**。

```lean
cyclicTensorPower M p : M.fiberOne ⟶ FunInfinity (BG (CyclicGroup p)) M.fiberOne
FunctorIso (cyclicTensorPower M p)
  (extendedPowerFunctor M p ≫ restrictAction (cycleEmbedding p))
FunctorIso (cyclicTensorPower M p (unit M)) (trivialAction (unit M))
```

土台・乗せ方：既存の有限置換・巡回群の準同型、BGへの前合成。群準同型の表現と単位対象の全作用の自明化を証明。

配置：`InfinityCategories/HA/InfinityOperads/ProductsAndCoproducts/CyclicPowers/`。

### P3-01　cofibrant複体の全tensor・弱同値（M）

原典：7.1.2.8,11; 4.1.7.6。素 700–1,400行、×2 **1,400–2,800行**。

```lean
cofibrantComplexMonoidal k : SymmetricMonoidalOrdinaryCategory
-- underlyingはprojective cofibrant複体、単位・全有限tensor・Koszul対称性を含む。
∀ X (f : Y ⟶ Z), Cofibrant X → Cofibrant Y → Cofibrant Z → QuasiIso f →
  QuasiIso (X ⊗ f) ∧ QuasiIso (f ⊗ X)
```

土台・乗せ方：EInfinity/ProjectiveModel、ProjectiveCofibrantUnit、ComplexLimits/CofibrantTensorQuillenとQuillen.tensor_isCofibrant。移動はOE-W1に調整。fの両端はcofibrant部分圏内として検収し、単なる片側左Quillenから全複体のK-flat性まで証明済みとしない。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra/ComplexModel/`。

### P3-02　対称モノイダル∞局所化（M）

原典：4.1.7.1–6; 2.2.1.9。素 3,000–6,000行、×2 **6,000–12,000行**。

```lean
monoidalLocalization (M : SymmetricMonoidalInfinityCategory)
  (W : System M.fiberOne) (hW : TensorStable W) :
  Σ L : SymmetricMonoidalInfinityCategory, MonoidalLocalizationData M L W
-- underlyingの∞局所化と、全monoidal関手準圏での普遍性・一意性。
```

土台・乗せ方：既存のIsLocalization・modelHammock_isLocalization・有限積と分類。多入力の局所化が全monoidal関手準圏の普遍性を持つまで証明する。ordinary LocalizedMonoidalだけでは不足。2.2.1.9等の必要なoperadic局所化の部分もこの費用に含む。

配置：`InfinityCategories/HA/AssociativeAlgebras/MonoidalModelCategories/Localization/`。

### P3-03　同じD(k)への構造の輸送（M）

原典：7.1.2.9,12; 4.1.7.5–6。素 1,000–2,200行、×2 **2,000–4,400行**。

```lean
derivedMonoidal (k : Type u) [CommRing k] : SymmetricMonoidalInfinityCategory
QCatEquivalence (derivedMonoidal k).fiberOne (derivedInfinityCategory k)
-- 同じ既存D(k)へ輸送。tensorの存在を外部instanceに置かない。
```

土台・乗せ方：既存derivedInfinityCategoryとそのdg nerve・projective模型の∞局所化の全比較。P3-02の結果のfiberOneをその同じD(k)へ輸送し、別の導来圏を新定義して終えない。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra/DerivedMonoidal/`。

### P3-04　任意arityのtensor・Koszul作用との比較（M）

原典：7.1.2.12; DAG XIII 2.2.1。素 1,600–3,000行、×2 **3,200–6,000行**。

```lean
tensorFixedComparison (M : Vertex (D k)) :
  FunctorIso (tensorRight (derivedMonoidal k) M) (tensorWith M)
equivariantTensorChainComparison k n :
  FunctorIso (localizeCofibrantTensorRepresentation k n)
    (cofibrantLocalization k ≫ extendedPowerFunctor (derivedMonoidal k) n)
-- Koszul符号・単位・全Σ_n作用・全射を照合。
```

土台・乗せ方：Project/DerivedCategories/Tensor/Fixed.lean、DGNerveTensorSimplexとNaturality、鎖のKoszul tensorPowerRepresentationFunctor。全単体の二変数候補だけを全arityの対称モノイダル構造としない。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra/TensorComparison/`。

### P3-05　導来tensorの変数別余極限保存（M）

原典：7.1.2.13 proof; 4.1.7.6。素 1,000–2,200行、×2 **2,000–4,400行**。

```lean
∀ X : Vertex (D k), PreservesSmallColimits (tensorLeft (derivedMonoidal k) X) ∧
  PreservesSmallColimits (tensorRight (derivedMonoidal k) X)
-- 固定Xの左Quillen性から、同じ全native図式の指定余錐へ橋を構成。
```

土台・乗せ方：D(k)の無条件のpresentability、projective tensorの左Quillen性と図式モデルの既存部品。ordinary derived functorの保存を同じnativeな余錐の保存へ接続する残量。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra/TensorColimits/`。

### P3-06　native compact＝perfectと生成（M）

原典：7.2.4.1–2,4,24–25。素 1,600–3,200行、×2 **3,200–6,400行**。

```lean
perfectInfinity k : FullSubcategory (D k) perfectPredicate
∀ X, IsCompactInfinity X ↔ IsPerfectInfinity k X
CompactlyGeneratedBy (D k) (integerShifts (derivedUnit k))
-- 係数kのD(k)で証明。一般E1環スペクトルへの拡張は別。
```

土台・乗せ方：dg moduleCompact_iff_perfect、finite-cell/retract、通常のcompact generator、D(k)の安定・presentable。nativeなMap(X,−)のfiltered保存への比較を追加し、三角圏の余積compactとの型差を埋める。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/FinitenessConditions/PerfectModules/`。

### P3-07　Perfの小さい模型・Ind表示（M）

原典：7.2.4.2; HTT 5.3.5.11。素 1,200–2,400行、×2 **2,400–4,800行**。

```lean
smallPerf k : SSet.{u}
QCatEquivalence (IndInfinity (smallPerf k)) (derivedInfinityCategory k)
-- 小さいretract閉な安定模型、指定Yoneda／包含と全比較。
```

土台・乗せ方：P3-06と既存のInd・小さい全部分準圏・代表の小ささ。Perf(k)の全包含・射・単位とInd延長の比較。P5のT_pそのもののKan延長・Eilenberg–Wattsは含めない。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/FinitenessConditions/PerfectInd/`。

### P3-08　一般可換代数上の相対tensor（E）

原典：4.5.2.1–2; 4.4.2。素 2,200–4,500行、×2 **4,400–9,000行**。

```lean
relativeModuleMonoidal M A (hgeom : HasGeometricRealizations M.fiberOne)
  (htensor : TensorPreservesGeometricRealizations M) : SymmetricMonoidalInfinityCategory
QCatEquivalence (relativeModuleMonoidal M A hgeom htensor).fiberOne (ModuleInfinity M A)
-- tensor=barによる相対tensor、assoc-bimodule表示との比較。
```

土台・乗せ方：P2-09の固定module、HA 4.4.2の実bar相対tensorと全実現の普遍性。通常balanced tensorは計算の材料。一般のA上のMod_AをD(k)のtensorの完成と混同しない。

配置：`InfinityCategories/HA/LeftAndRightModules/ModulesOverCommutativeAlgebras/SymmetricMonoidal/`。

### P3-09　Mod_HkとD(k)の対称モノイダル同値（C）

原典：7.1.2.13; 7.1.2.7。素 3,500–8,000行、×2 **7,000–16,000行**。

```lean
eilenbergMacLaneModuleEquivalence (k : Type u) [CommRing k] :
  SymmetricMonoidalEquivalence (ModuleSpectraMonoidal (Hk k)) (derivedMonoidal k)
-- 単位・全tensor・H^(-n)=π_n・Spへの忘却と同じV_kを照合。
```

土台・乗せ方：P3-03〜07と、別途実構成されたSp^⊗・Hk・Mod_Hkが前提。既存eilenbergMacLaneDerivedはその前提全部を供給しない。数値はそれらが供給された後の同値の比較費用である。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra/EilenbergMacLaneModules/`。

### P3-10　単位・係数作用・左右作用の接続（M）

原典：DAG XIII 2.2.5–6; 4.5.1。素 600–1,200行、×2 **1,200–2,400行**。

```lean
coefficientActionTransport (F : LaxSymmetricMonoidalFunctor M N)
  (A : CAlgInfinity M) (X : ModuleInfinity M A) :
  ModuleInfinity N (cAlgMap F A)
-- P2-08の単位と係数への特殊化・全評価比較。
-- Bの左k加群としての同定だけで右k作用を同一視しない。
```

土台・乗せ方：P2-08の特殊化と単位の全比較。P4/P5との受け渡し型を固定する。B≃k^{tC_p}はまず左作用を持つ同定で、Eilenberg–Wattsが与える右作用はP5から保持して受け取る。

配置：`InfinityCategories/HA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra/CoefficientActions/`。

## 4. 見積もりの集計と補正の意味

| 束 | 素 | ×2 |
|---|---:|---:|
| P1（E・Cを含む） | 9,500–17,600 | 19,000–35,200 |
| P2（E・Cを含む） | 13,700–26,800 | 27,400–53,600 |
| P3（E・Cを含む） | 16,400–34,100 | 32,800–68,200 |
| **30項目合計** | **39,600–78,500** | **79,200–157,000** |

| 使う範囲 | 項目数 | 素 | ×2 |
|---|---:|---:|---:|
| M：D(k)先行の構成と原典のための周辺 | 25 | 29,200–56,900 | 58,400–113,800 |
| E：P1-09・P2-06・P2-07・P3-08 | 4 | 6,900–13,600 | 13,800–27,200 |
| C：P3-09、Sp・Hk加群基盤の供給後 | 1 | 3,500–8,000 | 7,000–16,000 |

素の値は定義・全関手・全coherence・法則・比較・import・docstring・証明分割を含む。
既存の分類、D(k)のpresentability、projective模型、鎖のtensor、dg perfectを新造する量は再加算しない。
一方、分類からSegalが自動で出る、固定tensorから対称monoidal∞構造が出る、
ordinary compactからnative compactが定義上出る、という値引きもしない。

係数2はユーザー指定の両端への乗算であり、上端の保証ではない。
旧G12ではG01〜G03の上端3,200行に対しG01未完のまま18,959行を要した。
このため今回は構造・全族・比較を別々に素の値へ積み、さらに2を掛けた。
とくにP3-02の多入力局所化、P2-09のoperadic module、P3-06のcompact比較は外挿の大きい箇所。
新しい一般定理が必要と分かれば、ここで仮定を足して穴を隠さず段0を更新する。

一般のkで定義する部分と、P⁰がまず使うk=F_pでの比較を分ける。
F_pならflatnessの計算は簡単になるが、全arity・全自然性の費用まで消えるわけではない。
P3-09を未完成のまま後回しにする選択は、D(k)でP1〜P3の他の構成を先に進める順序の候補であり、
原典のMod_Hkとの一致や最終のSp値P⁰を不要と判断したものではない。
Sp・Hk・Mod_Hk自体の新造を含む総額は⑤aの経路比較と合算してから決める。

## 5. P⁰に要る最小出力と、P4〜P6への受け渡し

### 5.1 X^(⊗p)の全Σ_p作用

最初の出力はP2-03・P2-10の`C → Fun(BΣ_p,C)`とそのC_pへの制限。
sourceのCは同じD(k)、対象と射の全族を一つの関手にする。
各置換の鎖写像があるだけでは足りず、全BΣ_pの作用・合成・高次単体まで保持する。
DAGの`C^(p)`からの拡大冪の表示との全比較もP2-03に入れる。
既存のKoszul tensorPowerRepresentationFunctorはこの出力との計算用比較P3-04に使う。

### 5.2 乗法の等変性

最小の型はP2-04の`Fun(BΣ_p,C)`の中の`A^(⊗p) → trivial(A)`であり、Aについて全自然。
それをorbitへ送って、P2-05の`(A^(⊗p))_(C_p) → Sym^p(A) → A`を作る。
これでDAG XIII Remark 2.2.4の台の圏内の射を組み立てる入力になる。
EのP2-06〜07を追加すると、同じ射をCAlg内のfold・余積の普遍性として強く検収できる。
NS IV.1のE∞射としてのFrobeniusまで追う場合にはその強い出力も使う。
P⁰自体をCAlgの射にすることは要求しない（DAG XIII Warning 2.2.10）。

### 5.3 k^(tC_p)の作用

P1〜P3が供給するのは、P2-08〜09による「lax operadic関手が代数・加群を送る」型と、
P3-03の単位k・tensor・P3-10の係数比較。
P4からは同じFun(BC_p,D(k))上のTateと、少なくとも単位・係数moduleの像を作れる
**全coherentな**lax構造／作用の証人が必要である。

```text
-- ⑤aのP4が実際に構成する出力（今回の仮定追加ではない）
TateCp : FunInfinity (BG C_p) (D k) ⟶ D k
laxTateCp : LaxSymmetricMonoidalStructure TateCp
kTate : CAlgInfinity (derivedMonoidal k)
TateModule (X : FunInfinity (BG C_p) (D k)) : ModuleInfinity (derivedMonoidal k) kTate
FunctorIso (underlying TateModule) TateCp
```

最後のmoduleを使う場合、入力Xの自明k係数module構造から像を作る。
一般有限群やTate対角のlax性（NS III.3）まではP⁰のこの入力に必要ない。
しかし単位と二項pairingだけを用意して全結合・全単位のcoherenceを新たな仮定に置くこともできない。
NS I.3.1のSp上の証明をD(k)へ移すなら、その一般化またはMod_Hkとの比較も⑤a側と確認する。
Commのcoherenceも外部の新しい仮定にせずP2-09で証明する。
このTateの証明本体はP4でありP1〜P3の見積もりへ重複して入れていない。

さらにDAG XIII Example 2.2.5のBは**k-bimodule spectrum**である。
`B ≃ k^(tC_p)`は左k加群としての同定で、右作用まで通常の係数作用と等しいとは書かれていない。
P5でEilenberg–Wattsから得る右k作用と、P6の`e : k → B[-1]`の右moduleの型を保持する。
左作用だけの同定で右作用を置き換えて、P⁰をk線形と結論してはいけない。
同一視を省いたまま左右の型を満たす係数の全比較が、P3-10とP5/P6の境界となる。

### 5.4 最小でも省けないもの・後回しにするもの

省けないのは全Fin_*上の定義、同じD(k)の全monoidal局所化、全BΣ_p作用、
全自然な等変乗法、必要なhomotopy orbit、native Perf/Indと係数作用の接続。
省く候補は全Op∞のモデル構造、全colored/simplicial operadの整流、全EkにわたるMorita、
almost perfect・coherent環スペクトル、全可変底のmodule族、CAlgの全presentabilityを経る旧G12。
P⁰が必要な定理だけを証明することと、定義のcoherenceを弱めることを区別する。

## 6. HAを広く作る場合との差

上のMはP⁰へ向かう一つの構成経路であり、数学的に唯一の最小性を証明したものではない。
分類とSegalから直接作る道を採って、Cat∞のCartesian構造や一般局所化の証明を短縮できる可能性はあるが、
現時点ではその全比較を構成済みとしてP1-08・P3-02の見積もりを落とさない。

P1〜P3に関係する選定節の**一般の結果**まで広げると、30項目に加えて次の束が残る。
これらはCSVのF1〜F8の参照先であり、P⁰の型つき初期一覧30項目とは別の参考拡張枠。
各束は多くの原典項目を含み、実装するなら独立の段0と細分が必要。
以下の追加量は既に30項目で作った構成を再利用する差分としての粗い外挿である。

| 枠 | 原典・一般化する出力の型 | 素の追加 | ×2の追加 | 配置 |
|---|---|---:|---:|---|
| F1 | HA 2.1.1.1–7・19–27：`operadicNerve : FibrantSimplicialColoredOperad → InfinityOperad`、通常colored operadを含む全比較 | 3,500–7,000 | 7,000–14,000 | HA/InfinityOperads/Foundations/OperadicNerve |
| F2 | HA 2.1.4・2.4.4：`ModelCategory Preoperads`を実構成、wreath productの指定比較のoperadic弱同値性 | 6,000–12,000 | 12,000–24,000 | HA/InfinityOperads/Foundations/Preoperads、ProductsAndCoproducts/WreathProducts |
| F3 | HA 2.2.1・2.4の一般部分：色別反射・t構造・一般化operadに対する`OMonoidalLocalization`、弱近似の全制限同値 | 2,500–5,000 | 5,000–10,000 | HA/InfinityOperads/Constructions、ProductsAndCoproducts |
| F4 | HA 3.1・3.2：全small Oについて自由Algの左随伴、色別の全極限・sifted余極限の検出、`IsPresentable (AlgInfinity C O)` | 10,000–25,000 | 20,000–50,000 | HA/AlgebrasAndModulesOverInfinityOperads/FreeAlgebras、LimitsAndColimits |
| F5 | HA 4.1.7.7–19：全simplicial monoidal modelのoperadic nerveが指定局所化となる比較、前operad模型との全同定 | 4,000–8,500 | 8,000–17,000 | HA/AssociativeAlgebras/MonoidalModelCategories |
| F6 | HA 3.3・4.2.1の豊穣部分・4.5.3–4：`Mod(C)^⊗ → CAlg(C) × N(Fin_*)`の余Cartesian性、全base changeのmonoidal性・整流の仮定と比較 | 5,500–11,000 | 11,000–22,000 | HA/LeftAndRightModules/ModulesOverCommutativeAlgebras、およびAlgebrasAndModulesOverInfinityOperads/Modules |
| F7 | HA 7.1.2の一般Morita・全E_k、7.2.4.3・6–7：`Fun^L(Mod_R,C) ≃ Bimodules(R,C)`等の全関手圏の同値とperfect pairing | 6,500–15,000 | 13,000–30,000 | HA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra、FinitenessConditions |
| F8 | HA 7.2.4のalmost perfect・coherent・Tor amplitude・有限表示の一般判定：原典の全πと全切断を量化する述語・同値 | 4,500–9,500 | 9,000–19,000 | HA/AlgebraInTheStableHomotopyCategory/FinitenessConditions |
| **差分合計** | | **42,500–93,000** | **85,000–186,000** | |

30項目とこの参考拡張枠を単純に足すと、素82,100–171,500行、補正後 **164,200–343,000行**。
これは**HA全書の完成見込みではない**。326件は選定節と直接の周辺の照合であり、
2.2.2〜2.2.6・2.3の全体、3章の全 operadic Kan extension・tensor product、
5章以降の全E_k・Goodwillie・スペクトル基盤・付録などをすべて個別に見積もったものではない。
F4等に直接依存の節の参考量を含めるが、その節全体のnone/partialの今回の全再照合を主張しない。
HA全書を目標にするなら、2,866項目の既存対応表を基に別の一覧と段0が必要である。
F7の一般Moritaと、P5が実装する特定のEilenberg–Wattsを両方新造する二重計上も避ける。

P⁰に戻らない主な差は、全colored operadと全前operad模型、任意の可変係数・任意E_k、
almost perfectや全有限表示性の一般理論である。
これに対しHA 2〜3章の定義自体は省かず、同じ定義の必要な定理を先に証明する。

## 7. 使う前の配置整理（提案のみ、実際の移動なし）

D81のOE-W1は③-bの別作業。既に段1に含まれる一般の局所化・HomotopyWeight等はその取り込みを待ち、
⑤dの新実装と同時に別名へ動かさない。段2・PowerOperationのようにOE-W1の適用範囲外の候補は、
この紙を基に調整役が範囲を決める。以下の新パスは置き場所案であり、今回存在する移動済みファイルではない。

| 優先 | 現在の部品 | 置き場所案・残す部分 | 理由・使う項目 |
|---|---|---|---|
| 先行 | EInfinity/SimplicialLocalization/ModelHammockLocalization と周辺 | 一般のモデル局所化はHA/DerivedCategoryModelsのInvertingQuasiIsomorphisms、またはKerodonの∞局所化の該当節。モデル・フレーム自体はHomotopicalAlgebra | P3-02がEInfinity/BEの上位に依存しないようにする。**OE-W1段1と調整**。既存のIsLocalizationの仮定を保ち、HA 4.1.7.4全部として属性を付けない |
| 先行 | EInfinity/ProjectiveModel、ProjectiveCofibrantUnit、ComplexLimits/CofibrantTensorQuillen | ordinaryな非有界複体のprojective模型はHomologicalAlgebra/Cochain/ProjectiveModel。∞への橋だけHA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra | P3-01で使用。一般複体とBE代数のモデル転送を分ける。OE-W1段2の一般部分候補で、⑤dが今すぐ移す承認ではない |
| 先行 | InfinityCategories/Project/DerivedCategories/Tensor/Fixed とDGNerveTensor* | D(k)の∞ tensorの比較はHA/AlgebraInTheStableHomotopyCategory/StructuredRingSpectra/TensorComparison。一般dg nerveのtensor比較はKerodonのDifferentialGradedCategories、純鎖計算はDifferentialGraded | P3-03〜04。混在したProject配下を、一般dg nerve／導来∞／鎖の三層へ分類してから移す。全二変数候補と全monoidal構造の区別をdocstringに残す |
| 先行 | EInfinity/PowerOperation/TensorPowerRepresentation と、BarrattEccles/Theory/RepresentationComplexの一般部分 | DifferentialGraded/TensorPower/Representationへ一般の符号付き表現複体を抜く。operad作用を用いる箇所・May/P⁰固有の比較は元の側に残す | P2-03・P3-04。全Complex→Rep複体の関手はBE固有でない。operadのTensorNaturalityを丸ごとdgへ移すのではなく、依存を分離する |
| 維持 | CategoryTheory/Monoidal/Mod、HomologicalAlgebra/DerivedTensorMonoidal | 通常のbalanced tensor・boundedAboveのmonoidalは元の通常論の配置を維持 | P3-08の比較材料。HA∞のTheorem 4.5.2.1が証明済みという名前・属性に変えない |
| 維持＋橋を新設 | DifferentialGraded/Perfect/Compact、SmallEnhancement等 | dgの有限cell・retract・通常compactはDifferentialGradedに維持。native compactとの比較をHA/FinitenessConditionsへ新設 | P3-06〜07。dgの定理を移しただけでnative compact判定になったとはしない |
| 維持 | Kerodon/ClassificationOfCocartesianFibrations、CartesianFibrations、InnerFibrations/RelativeFunctor | Kerodonの該当節のまま | P1-03〜10、P2-01。既存分類をHAへ複製しない。必要なoperadicな特殊化だけHAへ |
| 維持 | HA/Monadsの179本、EInfinity/BarrattEccles、Interface | 今回のP1〜P3の移動・再開対象にしない | G12の停止を維持。BEの整流の計算材料とHAのCAlgの定義を分ける |

整理は元→新のファイル・宣言の対応表を作り、引用属性・import・他枝の利用を確認してから行う。
今回の型つき一覧の見積もりは数学・構成・比較の追加行数であり、
OE-W1の大規模な移動・保存比較・全監査のコストは含まない。
移動だけを行う将来作業で必要なビルド・監査も、この「紙・ビルドなし」のターンでは実行しない。

## 8. 次の判断に渡す順序・検収点

1. OE-W1の一般局所化の整理と、P3-01に使うprojective複体の場所を先に調整する。
2. P1-01〜07・10でFin_*・operad・対称monoidal定義・ordinary nerveを作り、
   P2-01の**抽象Algの定義**をここで先に構成し、その後でP1-08のCat∞上の可換代数表示と
   P3-02の原典の一般局所化に必要な範囲を接続する。D(k)を先に必要とする循環にはしない。
3. P3-01〜05で同じD(k)の全構造と既存tensorへの比較を検収。
4. P2-01〜05・10でHA-CAlg、全等変冪・乗法・orbitの射を出す。
5. P2-09→P2-08、P3-06〜07・10を進め、⑤aのP4〜P6との係数・Perf/Indの型を接続する。
6. Eの4項目を先に入れるか、P3-09のSpへの比較をどの段で供給するかはユーザーが選ぶ。

ここで承認を求める外枠やLean再開の指示は作らない。今回の停止点は**紙の段0のコミット**。
原典の定義を維持した必要な出力・まだ必要な外部入力・個別費用と配置の候補を判断材料として渡す。

## 9. 今回の検収

基準mainからの変更はこの報告と二つの個別照合CSVのみ。
p0-mapの該当9件、HA対応表の326件の集合・重複なし・status・元の型差の保持、
初期一覧30項目と型・素の値・係数2・集計の一致、配置先・参照元を確認した。
実装済みの新項目は0、Lean・drafts・既存対応表・HTMLは変更していない。
ビルド・公理監査・共有の鍵の取得も行っていない。報告を自枝にコミットして止まる。

P1〜P3実装一覧：**済み 0／全体 30（うち追加 0）**。段0の紙のみ完了、Lean未着手。
