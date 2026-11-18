-- 将来の置き場所：SerrePositivity.BhattScholze.Prismatic.CrystallineInput（仮。原典 Thm 5.2・Lemma 5.4・Cor 5.5 の (Z_p,(p))・多項式・mod p の場合）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md §10（D68 改訂後の経路、11-07）・§9、単位 A1-2／A1-3／A1-5。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.PolynomialCategory
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechFrameHomotopy
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
public import SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.CompletedPDEnvelope

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCohomology
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamBicomplex
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumn
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamColumnPoincare
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCartierAssembly
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDModelReduction
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.CartierCompletedForms
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.FinitePolynomialCartier

public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.FrobeniusCechComparison
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCoordinates
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridgePushout
import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDIntegral
import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraModel
import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBridge
import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
public import SerrePositivity.EInfinity.BarrattEccles.CAlgAlgebraSource
public import SerrePositivity.EInfinity.BarrattEccles.DiscreteAlgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CommutativeAlgebraFunctor
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.RingTheory.DividedPowers.Basic
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyPrecomposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
-- 本ファイルは drafts/A1/HodgeTateMap.lean（小さい Čech 模型 `htRings`・`reducedModel`、η⁰・η¹、`HodgeTateIsoStatement`、`formVars`）、
-- drafts/A0/PrismaticEnvelope.lean（`completedFreeDelta`）、drafts/Shared/{DeRhamPolynomial,CosimplicialCupProduct,CosimplicialEInfinity}.lean と本体の `HomologicalAlgebra/Cosimplicial/BocksteinClass` を使う
-- （CosimplicialEInfinity は 11-07 の §10.5 の部品：`strictShapeNerve`・`strictNatTransFunctorIso`・`totCDGAFunctor`）。
-- A1/HodgeTateComparison と A1/DeRhamComparisonPoly の両方がこれを import する（W9-III-09）。

/-!
# 結晶側の計算（BS 著者版 Thm 5.2・Lemma 5.4・Cor 5.5 の (Z_p,(p))・R = F_p[X_1,…,X_r]・mod p の場合）

## 概要
**D68 改訂（2026-11-05 夜、ユーザー）**：以前の黒箱 `crystalline_deRham_polynomial_Zp`（関手 ∞ 圏の同型 Δ ≃ Ω̂、恒久の引用）は外した。
使う側が実際に要るのは対象ごとの命題 `HodgeTateIsoStatement`（Čech–Alexander 模型 Tot(C^•/p) の H^i で η^i が全単射）だけなので、
それを mod p で直接証明する（`hodgeTate_of_deRham_cartier`）。段は六つ（a1-design §10）：
1. Lemma 5.4（`frobeniusTwist_cech_quasiIso`、無限変数は `frobeniusTwist_cech_quasiIso_infinite`、G-A1-15）。
2. C^•/p → D^•/p が cohomology 同型（`crystallineBridgeModP_isCohomologyIso`。D^n/p ≅ C^n/p ⊗_{B^n/p, φ} B^n/p）。
3. D_0^•/p → D^•/p が cohomology 同型（`pdInclusionModP_isCohomologyIso`、G-A1-16）。
4. H^*(D_0^•/p) ≅ H^*(Ω^•_{F_p[X]})（`pdDeRhamCohomologyIso`。双複体 Ω^j_pd(D_0^n)：列は pd Poincaré G-A1-7、j ≥ 1 の行は BdJ の収縮 G-A1-14）、cup 積と両立。
5. n 変数の Cartier 同型（`finitePolynomialCartier`）。
6. 生成元での照合（`crystallineChain_generators`）。
後半（`pdModel` 以下の J つき模型・`formsCAlg`）は A1-5（D69、A1/DeRhamComparisonPoly）用で、上の経路では
`pdModel`・`pdRow`・`withExtraCoords`・`splitDeltaCoordinatesModP`・`insertPdFactor` を使う。

## 方針
mod p なので導来 Nakayama（G-A1-4）は使わない。比較はすべて余単体的可換環の厳密な射（または整係数の厳密な射の mod p）で与え、
cohomology の cup 積は `cohomologyMap_cup` で、Bockstein は `bockstein_natural` で自動的に移る。∞ 圏の部品は使わない。

## 規約
恒久の引用はない（段階 II は sorry 0）。基底は ℤ_p（`crystallineBase`、ULift）、F_p は `cartierBase`。
「cohomology 同型」は `Cosimplicial.IsCohomologyIso`（全次数で `cohomologyMap` が全単射）。

## 使われ方
A1-3：`hodgeTate_iso_polynomial_Zp`（A1/HodgeTateComparison）。A1-5：後半の模型と大きい模型 `wittBigPdModel`（A1/DeRhamComparisonPoly）。
-/

@[expose] public section
noncomputable section
universe u

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})
open CategoryTheory CategoryTheory.Limits SSet MonoidalCategory
open scoped Simplicial TensorProduct

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.InfinityCategories SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion SerrePositivity.Cosimplicial
open SerrePositivity.BhattScholze.PerfectoidizationInterface
attribute [local instance] HasDerivedCategory.standard
variable (p : ℕ) [Fact p.Prime]

/-- 有界基底 A は p 完備。ℤ_(p)→A を ℤ_p へ延長する標準係数射。 -/
def padicCoefficientMap {A : Type u} [CommRing A] (P : OrientedPrism p A) : crystallineBase.{u} p →+* A := by
  sorry -- ℤ の主元完備化の普遍性と P.complete_p。ULift を介して係数を読む

abbrev changePolyNerve {k l : Type u} [CommRing k] [CommRing l] (f : k →+* l) :=
  (SSet.uliftFunctor.{u+1,u}).map (nerveMap (changePoly f))

/-! ## 連続 de Rham 複体の CAlg 値（A1-5・D69 用。D68 改訂後の経路では使わない） -/

/-- 連続 de Rham 複体に単位・外積を入れた通常の可換モノイド複体。 -/
abbrev formComplex (k : Type u) [CommRing k] (n : ℕ) :=
  (DeRham.completedDeRhamComplex k (formVars.{u} n) p).extend ComplexShape.embeddingUpNat

def formUnit (k : Type u) [CommRing k] (n : ℕ) : 𝟙_ (Complex k) ⟶ formComplex p k n := by
  sorry -- 次数 0 では a↦a·1、他の次数では零。d̂(1)=0
def formProduct (k : Type u) [CommRing k] (n : ℕ) :
    formComplex p k n ⊗ formComplex p k n ⟶ formComplex p k n := by
  sorry -- (i,j) のテンソルを completedWedge で i+j へ送る。鎖写像条件は completedDeRhamD_wedge
def formsCDGA (k : Type u) [CommRing k] (n : ℕ) : CommMon (Complex k) := by
  let X := formComplex p k n
  letI : MonObj X := {
    one := formUnit p k n
    mul := formProduct p k n
    one_mul := by sorry -- 1∧ω
    mul_one := by sorry -- ω∧1
    mul_assoc := by sorry -- 完備外積の結合律
  }
  letI : IsCommMonObj X := by sorry -- 外積の次数付き可換性
  exact ⟨X⟩

def formsCDGAFunctor (k : Type u) [CommRing k] : Poly k ⥤ CommMon (Complex k) where
  obj Q := formsCDGA p k Q.n
  map f := by sorry -- 係数は f、dX_j↦d(f(X_j))。外積で延長した連続鎖写像
  map_id := by sorry -- 完備自由形式の基底で恒等
  map_comp := by sorry -- 変数の代入の連鎖律

abbrev formsBEFunctor (k : Type u) [CommRing k] :=
  formsCDGAFunctor p k ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeAlgebraFunctor k ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.restrictAlgebra (augmentation k)
def formsNerve (k : Type u) [CommRing k] :
    (SSet.uliftFunctor.{u+1,u}).obj (polyNerve k) ⟶ nerve (operad k).Algebra where
  app n := ↾fun q => ((formsBEFunctor p k).mapComposableArrows _).obj q.down
  naturality := by sorry -- 射列の制限と後合成
def formsCAlg (k : Type u) [CommRing k] :=
  Cosimplicial.strictShapeNerve (formsCDGAFunctor p k) ≫ Cosimplicial.cdgaCAlg (E := E) k
abbrev formsVertex (k : Type u) [CommRing k] (n : ℕ) :=
  (formsCAlg (E := E) p k).app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (⟨n⟩ : Poly k)))

abbrev polyPoint (k : Type u) [CommRing k] (n : ℕ) :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (⟨n⟩ : Poly k))

/-! ## 結晶の多項式模型（G-A1-14・16・17）。D68 改訂後の経路は `pdModel`・`pdRow`・`withExtraCoords`・`splitDeltaCoordinatesModP`・
`insertPdFactor` を使う。 -/

-- 未完備 pd 模型は本体の PDPolynomialCech に置く。

-- 完備 pd 模型は本体の PDCompletedCech に置く。

-- pdRow と正次数の行の収縮は本体の PDDeRhamRow に置く。

-- 高次座標の Čech 模型は本体の CrystallineExtraModel に置く。

/-- δ^a(X) の a≥1 の座標を独立に残した pd envelope。
自由 δ 環で各 z=X^(i)−X^(0) の φ(z)/p を添加する Cor 2.39 の模型。 -/
abbrev deltaCopies (r n : ℕ) := formVars.{u} r × Fin (n+1)
def deltaCopyX (r n : ℕ) (a : deltaCopies.{u} r n) :=
  let Z := crystallineBasePrism.{u} p
  pdCompletionUnit (RelativeFreeDeltaRing (R := crystallineBase p) (deltaCopies r n)) p
    (algebraMap (crystallineBase p) _ Z.generator) (MvPolynomial.X (a,0))

-- 結晶側の完備 p 除算模型は本体の CrystallinePDModel に置く。

def splitDeltaCoordinates (r : ℕ) :
    pdDeltaModel.{u} p r ≅ withExtraCoords p (crystallineBase.{u} p) r := by
  sorry -- G-A1-16。差の divided powers は δ⁰ 座標だけ。δ^(a+1)(X) は各 copy の
        -- 通常の多項式変数。これらの像は余面・余退化に自然

-- pd 因子の包含は本体の CrystallineExtraModel に置く。

def pdComplex (k : Type u) [CommRing k] (D : Cosimplicial.CosimplicialAlgebra k) :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (D ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule k)

/-- 概要：G-A1-16 の整係数版：D_0^• → D^•（追加の δ 座標の Čech 因子の挿入）は交代余面複体の擬同型。
方針：E^• = Q^{⊗(•+1)} の extra degeneracy（U_k ↦ 0）、D_0^• とのテンソル、各 mod p^a の収縮の Rlim。
規約：D68 改訂後の経路は mod p 版 `pdInclusionModP_isCohomologyIso` を使う。
使われ方：A1-5 の `wittSmallBridge_isInvertible`（W(A_0/d_0) 上の Thm 5.2 β、旧 `wittPdBridge`）。 -/
theorem extraCech_comparison (r : ℕ) :
    let k := crystallineBase.{u} p
    QuasiIso ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (insertPdFactor p k r) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule k))) := by
  sorry -- G-A1-16。k→Q は正の δ 座標を 0 に送る切断をもち、E^• は増大付きで収縮する。
        -- D₀^• とテンソルし各 mod p^a の収縮を Rlim。j=0 の pd 行そのものは収縮させない

/-- 元の一般係数環上のpd模型の関手。追加の分冪・完備性の仮定を持つ本体版とは別に、未証明の構成を保持する。 -/
def pdModelPolynomialFunctor (k : Type u) [CommRing k] : Poly k ⥤ Cosimplicial.CosimplicialAlgebra k where
  obj Q := pdModel p k Q.n
  map f := by sorry -- 各 copy で f を代入、差の divided powers を保つ延長
  map_id := by sorry -- pd 包の普遍性
  map_comp := by sorry -- 同じ延長の一意性

-- 11-07：旧 `pdTotMap`・`PDPolynomialComparison`・`pdPolynomialComparison`（G-A1-17、1 単体までの自然性）は
-- D69 の大きい模型（a1-design §10.5）に置き換えたので削除（ユーザー決定）。

/-! ## A1-5（D69）用：枠つきの J つき pd Čech 脈体と、厳密に関手的な小さい模型の de Rham 比較（a1-design §10.5、11-07）

基底 (k, J, γ) と k/J 上の代数 R̄、添字集合 S と s : S → R̄（枠 k[S] → R̄）について、枠の Čech 脈体 k[S × [n]] → R̄ の核の p 完備な
J つき pd 包 D_S^• を置く（選択は対象だけ、射は普遍性の lift なので厳密に関手的）。D69 の大きい模型（S = Q^∧ の台集合）と、小さい模型
`pdModel k r`（S = Fin r）はどちらもこの形。枠の取り替えは Tot の擬同型（表示によらない、`pdCechNerveMap_quasiIso`）。
小さい模型は k 上の `Poly k` について厳密に関手的（係数の持ち上げが要らない）なので、de Rham 比較は k = C の上で関手として行う。 -/

/-- 概要：余単体的 cdga K(Q)^n = Ω^•_pd(D_0^n)（D_0^• = `pdModel k Q.n`）を Q ∈ Poly k について厳密な関手に。
方針：各項は `pdRow` の行（j 次）を `pdDeRhamDifferential` でつなぎ、外積で cdga に。Q → Q′ は `pdModelPolynomialFunctor` の射と
dX ↦ d(f(X)) の外積への延長（pd 微分と可換）。係数は k のまま（持ち上げは要らない）なので厳密に関手的。
規約：`Cosimplicial.CosimplicialCDGA k`（Shared/CosimplicialEInfinity）。
使われ方：`pdDeRhamFunctorIso`。 -/
def pdDeRhamCDGA (p : ℕ) (k : Type u) [CommRing k] : Poly k ⥤ Cosimplicial.CosimplicialCDGA k := by
  sorry -- n ↦ (⊕_j pdRow p k Q.n j, pdDeRhamDifferential, 外積)。射は pdModelPolynomialFunctor と連鎖律

/-- 概要：形式の次数 0 への射影 Ω^•_pd(D_0^n) → Ω^0 = D_0^n（Ω^{≥1} は dg イデアル、商は微分零の次数 0）を Q について自然に。
方針：各項で商写像。鎖写像・乗法的・余単体的。
規約：右辺は `pdModelPolynomialFunctor` を次数 0 の cdga（`Cosimplicial.discreteCDGA`）とみたもの。
使われ方：`pdDeRhamFunctorIso`（総複体 → 行 0 の擬同型）。 -/
def pdDeRhamProjection (k : Type u) [CommRing k] :
    pdDeRhamCDGA p k ⟶ pdModelPolynomialFunctor p k ⋙
      (Functor.whiskeringRight SimplexCategory _ _).obj (Cosimplicial.discreteCDGA k) := by
  sorry -- 各 (Q, n) で Ω^•_pd → Ω^0。pdModelPolynomialFunctor の射と両立

/-- 概要：K(Q)^0 = Ω^•_pd(D_0^0) は連続 de Rham 複体 Ω̂^•_{k⟨X⟩/k}（D_0^0 = k⟨X⟩、差がないので pd 微分は通常の微分）。Q について自然な同型。
方針：`pdTerm k r 0` = k[X] の p 完備化、`pdRow` の j 次 = Ω̂^j。
規約：右辺は `formsCDGAFunctor`。
使われ方：`pdDeRhamFunctorIso`（列 0 への射影の行き先）。 -/
def pdDeRhamZeroIso (k : Type u) [CommRing k] :
    pdDeRhamCDGA p k ⋙ (evaluation SimplexCategory (CommMon (Complex k))).obj ⦋0⦌ ≅ formsCDGAFunctor p k := by
  sorry -- 項ごとに pdRaw k r 0 = k[X] ⊗ Γ(0) = k[X]、formVars と Fin r の同一視

/-- 概要：行 0 への射影は Tot で可逆：Tot K(Q) → Tot D_0(Q)^• は擬同型。
方針：射影の核は j ≥ 1 の行からなる部分複体。j についての有限な filtration（各総次数で有限）で、各段は収縮可能な行
（`pdRow_contractible`、一般の k）。U : CAlg → D(k) は保存的なので CAlg の辺も可逆。
規約：**注意**（§10.5 の 6）：行 0 の**包含**は鎖写像ではない（縦の微分が消えない）。使うのは総複体 → 行 0 の**射影**。
使われ方：`pdDeRhamFunctorIso`。 -/
theorem pdDeRhamProjection_isInvertible (k : Type u) [CommRing k] (Q : Poly k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk ((pdDeRhamProjection p k).app Q)).map (Cosimplicial.totCDGAFunctor (E := E) k)).toTruncated := by
  sorry -- 核 ⊕_{j≥1} の j-filtration と pdRow_contractible。totCDGA の下の複体は総複体

/-- 概要：K(Q) はホモトピー的に定数：全ての余単体的構造射 Ω^•_pd(D_0^m) → Ω^•_pd(D_0^n) は擬同型。
方針：pd Poincaré 補題（G-A1-7、`pdPoincare_column` の一般の k 版）：各 Ω^•_pd(D_0^n) は copy の任意の一つから Ω̂^•_{k⟨X⟩} に擬同型で、
余面は copy を copy へ送る。
規約：k は一般（pd 多項式の de Rham 複体の収縮は係数によらない、p 完備化は mod p^a ごと）。
使われ方：`pdDeRhamFunctorIso`（列 0 への射影の可逆性）。 -/
theorem pdDeRham_homotopicallyConstant (k : Type u) [CommRing k] (Q : Poly k)
    {m n : SimplexCategory} (θ : m ⟶ n) : QuasiIso (((pdDeRhamCDGA p k).obj Q).map θ).hom.hom := by
  sorry -- G-A1-7：一変数 pd Poincaré の Künneth を copy ごとに。p 完備化は mod p^a で

/-- 概要：`formsCAlg` は厳密な関手 `formsCDGAFunctor` の `strictShapeNerve` と `cdgaCAlg` の合成。
方針：同じ厳密なcdga関手を、選んだTheoryのcdga実現で読む定義から。
規約：等式。
使われ方：`pdDeRhamFunctorIso`。 -/
theorem formsCAlg_eq (k : Type u) [CommRing k] :
    formsCAlg (E := E) p k = Cosimplicial.strictShapeNerve (formsCDGAFunctor p k) ≫ Cosimplicial.cdgaCAlg (E := E) k := by
  rfl

/-- 概要：k 上の小さい模型の de Rham 比較を**関手 ∞ 圏の同型**として：Tot_{E∞} D_0(−)^• ≅ Ω̂^•_{(−)/k}（Fun(N(Poly k), CAlg_k)）。
D69 の段 6（a1-design §10.5）。
方針：厳密に自然な span Tot D_0^• ← Tot K → K^0 = Ω̂^•：
(a) `totCDGA_discrete`（次数 0 の cdga の Tot は余単体的可換環の Tot）、(b) 行 0 への射影 `pdDeRhamProjection`（成分は
`pdDeRhamProjection_isInvertible`）を `strictNatTransFunctorIso` で、(c) 列 0 への射影 `totCDGA_evalZero`（`stableHomotopyPrecomp` で
前合成、成分は `pdDeRham_homotopicallyConstant` と `totCDGA_evalZero_isInvertible`）、(d) `pdDeRhamZeroIso`、(e) `formsCAlg_eq`。
規約：k は任意（A1-5 では k = C = A₀/d₀）。`pdModelPolynomialFunctor k` は Poly k 上で厳密に関手的（射は k 係数のまま代入、pd 包の普遍性）。
使われ方：DeRhamComparisonPoly の `bigZigzagIso`。旧 `pdPolynomialComparison`（1 単体までの自然性）に代わる。 -/
def pdDeRhamFunctorIso (k : Type u) [CommRing k] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k) ≫ Cosimplicial.totEInfinityFunctor (E := E) k)
      (formsCAlg (E := E) p k) := by
  let disc := (Functor.whiskeringRight SimplexCategory _ _).obj (Cosimplicial.discreteCDGA k)
  let ev0 := (evaluation SimplexCategory (CommMon (Complex k))).obj ⦋0⦌
  -- (a) Tot(D_0 を次数 0 の cdga に) ≅ Tot_{E∞} D_0
  let ea : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k ⋙ disc) ≫ Cosimplicial.totCDGAFunctor (E := E) k)
      (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k) ≫ Cosimplicial.totEInfinityFunctor (E := E) k) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((Cosimplicial.totCDGA_discrete (E := E) k).precomp (Cosimplicial.strictShapeNerve (pdModelPolynomialFunctor p k)))
      (by rw [Cosimplicial.strictShapeNerve_comp]; rfl) rfl
  -- (b) Tot K → Tot(行 0)
  let eb := Cosimplicial.strictNatTransFunctorIso (pdDeRhamProjection p k) (Cosimplicial.totCDGAFunctor (E := E) k)
    (pdDeRhamProjection_isInvertible (E := E) p k)
  -- (c) Tot K → K^0
  let ec : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Cosimplicial.strictShapeNerve (pdDeRhamCDGA p k) ≫ Cosimplicial.totCDGAFunctor (E := E) k)
      (Cosimplicial.strictShapeNerve (pdDeRhamCDGA p k ⋙ ev0) ≫ Cosimplicial.cdgaCAlg (E := E) k) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableHomotopyPrecomp (Cosimplicial.strictShapeNerve (pdDeRhamCDGA p k)) (Cosimplicial.totCDGA_evalZero (E := E) k))
      (by sorry)) -- 頂点 ULift.up (nerveVertex Q) で totCDGA_evalZero_isInvertible と pdDeRham_homotopicallyConstant
      rfl (by rw [Cosimplicial.strictShapeNerve_comp]; rfl)
  -- (d) K^0 ≅ Ω̂（厳密な同型）
  let ed := Cosimplicial.strictNatTransFunctorIso (pdDeRhamZeroIso p k).hom (Cosimplicial.cdgaCAlg (E := E) k) (by
    sorry) -- 同型の成分の nerve 辺は可逆（逆の辺と二つの 2 単体）
  exact ea.symm ≪≫ eb.symm ≪≫ ec ≪≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ed rfl (formsCAlg_eq (E := E) p k).symm

/-! ## D68 改訂後の経路：(Z_p,(p))・F_p[X_1,…,X_r] の HT 比較を mod p で直接（a1-design §10） -/

abbrev cartierComplex (n : ℕ) := DeRham.deRhamComplex (cartierBase.{u} p) (formVars.{u} n)

/-! ### 段 1：Lemma 5.4（Frobenius ひねりの Čech 脈体） -/

-- 有限・無限変数の比較は本体の FrobeniusCechComparison に置く。

/-! ### 段 2：C^•/p → D^•/p -/

-- 結晶の橋とその mod p は本体の CrystallineBridge に置く。

-- Frobenius 押し出しと橋の同型は本体の CrystallineBridgePushout に置く。

/-! ### 段 3：D_0^•/p → D^•/p（G-A1-16） -/

-- pdRings と mod p の包含は本体の CrystallinePDInclusion に置く。
-- 整係数の包含とその還元との一致は CrystallinePDIntegral に置く。

/-! ### 段 4：H^*(D_0^•/p) ≅ H^*(Ω^•_{F_p[X]}) -/

-- pdModel_modP は本体の PDModelReduction に置く。

-- pdDeRhamDifferential と pdDeRhamDoubleComplex は本体の PDDeRhamBicomplex に置く。

@[no_expose] private def pdColumn_complex_eq (r n : ℕ) :
    (pdDeRhamDoubleComplex p (cartierBase.{u} p) r).X n =
      pdDeRhamColumn p (cartierBase.{u} p) r ⦋n⦌ := by
  dsimp only [pdDeRhamDoubleComplex, HomologicalComplex₂.ofGradedObject, pdDeRhamColumn] <;> rfl

/-- 概要：列 n への Ω^•_{F_p[X]} の包含（copy 0 の座標 X^{(0)} と dX^{(0)}）。
方針：多項式 ↦ copy 0 の多項式、dX ↦ dX^{(0)}。
規約：どの copy を使っても余単体的に同じクラス。
使われ方：`pdPoincare_column`。 -/
@[no_expose] def pdColumnInclusion (r n : ℕ) :
    cartierComplex.{u} p r ⟶ (pdDeRhamDoubleComplex p (cartierBase.{u} p) r).X n :=
  pdDeRhamPolynomialInclusion p (cartierBase.{u} p) r (cartierBase_natCast p) ⦋n⦌ ≫
    eqToHom (pdColumn_complex_eq p r n).symm

@[no_expose] private def pdPoincare_column_proof (r n : ℕ) :
    QuasiIso (pdColumnInclusion.{u} p r n) := by
  letI : QuasiIso (pdDeRhamPolynomialInclusion p (cartierBase.{u} p) r (cartierBase_natCast p) ⦋n⦌) :=
    pdDeRhamPolynomialInclusion_quasiIso p (cartierBase.{u} p) r (cartierBase_natCast p) ⦋n⦌
  change QuasiIso (pdDeRhamPolynomialInclusion p (cartierBase.{u} p) r (cartierBase_natCast p) ⦋n⦌ ≫
    eqToHom (pdColumn_complex_eq p r n).symm)
  infer_instance

/-- 概要：G-A1-7：pd Poincaré 補題：列 n（Ω^•_pd(B_0⟨z_1,…⟩_pd)、B_0 = F_p[X^{(0)}]）は Ω^•_{F_p[X]} に擬同型。
方針：一変数の Ω^•_pd(B⟨z⟩/B) ≃ B（dγ_m(z) = γ_{m−1}(z)dz で γ_m(z) の項が消える）をテンソルで。
規約：標数 p でも成り立つのは pd 微分を使うから。
使われ方：段 4。 -/
theorem pdPoincare_column (r n : ℕ) : QuasiIso (pdColumnInclusion.{u} p r n) :=
  pdPoincare_column_proof p r n

/-- 概要：段 4：H^i(D_0^•(F_p)) ≅ H^i(Ω^•_{F_p[X]/F_p})。
方針：双複体 `pdDeRhamDoubleComplex` の総複体 T を経由する span（**11-07 訂正**：行 0・列の包含は鎖写像でないので射影を使う、a1-design §10.3）：
T → 行 0（= D_0^•、j = 0 成分への射影）は核が j ≥ 1 の行の有限 filtration で、行の収縮（`pdRow_contractible`）により擬同型、
T → 列 0 = Ω^•（n = 0 成分への射影）は列がホモトピー的に定数（`pdPoincare_column`、余面は H で同じ同型）なので擬同型。
Bockstein との両立（段 6）のため、同じ span を ℤ_p 上の厳密な写像 Tot D_0^• ← T_{ℤ_p} → Ω^•_{ℤ_p⟨X⟩} として作り、各項 p ねじれなしの mod p として得る。
規約：加法群の同型。積との両立は `pdDeRhamCohomologyIso_cup`。
使われ方：段 6 の `crystallineChain`。 -/
def pdDeRhamCohomologyIso (r i : ℕ) :
    cohomology (pdModel.{u} p (cartierBase.{u} p) r ⋙ Under.forget (CommRingCat.of (cartierBase p))) i ≃+
      (cartierComplex p r).homology i :=
  pdDeRhamCechToPolynomial p (cartierBase.{u} p) r (cartierBase_natCast p) i

/-- 概要：段 4 の同型は cup 積と外積に両立する。
方針：総複体 T に、余単体の方向は厳密な Alexander–Whitney（`cup`）、形式の方向は外積、Koszul 符号の積を入れ、T → 行 0 と T → 列 0 = Ω^• の射影が
dg 環の射であることを示す（a1-design §10.3。T の積の結合律は鎖のレベルで、可換性は cohomology で）。
規約：右辺の積は `DeRham.deRhamCohomologyWedge`。
使われ方：段 6 の `crystallineChain_cup`。 -/
theorem pdDeRhamCohomologyIso_cup (r : ℕ) {i j : ℕ}
    (a : cohomology (pdModel.{u} p (cartierBase.{u} p) r ⋙ Under.forget (CommRingCat.of (cartierBase p))) i)
    (b : cohomology (pdModel.{u} p (cartierBase.{u} p) r ⋙ Under.forget (CommRingCat.of (cartierBase p))) j) :
    pdDeRhamCohomologyIso p r (i+j) (cohomologyCup _ a b) =
      DeRham.deRhamCohomologyWedge _ _ (pdDeRhamCohomologyIso p r i a) (pdDeRhamCohomologyIso p r j b) :=
  pdDeRhamCechToPolynomial_cup p (cartierBase.{u} p) r (cartierBase_natCast p) a b

/-! ### 段 5：n 変数の Cartier 同型 -/

-- 有限 Cartier と生成元の代表形式は本体の FinitePolynomialCartier に置く。

/-! ### 段 6：生成元での照合と組み立て -/

-- cartierFormsIso は本体の CartierCompletedForms に置く。

-- crystallineChain と crystallineChain_cup は本体の CrystallineChainProduct から使う。

-- crystallineChain_generators は本体の CrystallineGeneratorClasses に置く。
-- 総複体で p で割った整係数の微分を還元し、第 0 行では Bockstein、第 0 列では一次 Cartier 類を得る。
-- hodgeTate_of_deRham_cartier は本体の HodgeTateCartierAssembly に置く。

end SerrePositivity.BhattScholze.Prismatic
