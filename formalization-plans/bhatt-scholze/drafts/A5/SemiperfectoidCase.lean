-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Descent.SemiperfectoidCase（仮。原典 Prop 8.5 の証明 (4)、系 3、G-A5-17）
-- 設計書：formalization-plans/bhatt-scholze/a5-design.md §3.4、単位 A5-2。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Semiperfectoid.Basic

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.Transfinite.Tower
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity
public import SerrePositivity.BhattScholze.Semiperfectoid.CompatibleRootPerfectoid
-- 本ファイルは drafts/A5/PerfectSite.lean（比較写像。W9-III-09：PerfectSiteComparison＝Prop 8.5 の証明は本ファイルより後）、drafts/A4/{Perfectoidization,InterfaceFields}.lean、drafts/A3/LciAndQuasiregular.lean、
-- drafts/A2/{HodgeTateFiltration,BaseChangeAndTensor}.lean、drafts/DerivedGeneral/Truncation.lean を import する。
-- 導来 p 完備性は drafts/A7/AnimatedDomain.lean、G-A7-5 の芯は drafts/A7/DiscreteCore.lean（W9-II-24：UniversalProperty ではなく A5 より先に置く独立ファイル）を import する。

/-!
# semiperfectoid の場合（BS 著者版 Prop 8.5 の証明 (4)）

## 概要
S が semiperfectoid（離散）なら Δ_{S/A,perf} は連結かつ coconnective、よって離散な完全 prism で、S_perfd = Δ_{S/A,perf}/d は perfectoid 環。
さらに S → S_perfd は全射で、S_perfd は Cor 7.3 の普遍 perfectoid 環 R′ に S の下で同型（Prop 8.5 の系 3）。

## 方針
連結性は HT filtration（A2-3）と semiperfectoid の余接複体（L_{S/R}^∧[−1] 連結）。S → S_perfd → R′ の合成は Thm 7.4 で全射、第二の射は
R′ の普遍性で分裂全射、S → S_perfd の全射性は原典どおり：perfectoid R_1 → S 全射に取り替え（G-A5-17：余接複体が変わらないので Δ も変わらない）、
Thm 7.14 で核の生成元 f_j が p 冪根の系をもつ R_1′ に移り、S′ = R_1′⟨X_j^{1/p^∞}⟩/(X_j) → S の HT での全射性、J 有限への帰着、Prop 7.10（A3-4）。

## 規約
semiperfectoid は「p 完備で perfectoid 環の商」（既存の `exists_perfectoidization_of_semiperfectoid_quotient` の仮定の形に合わせる）。
R′ は既存の普遍 perfectoid 化（`IsPerfectoidization`）。

## 使われ方
A5-4 の弱始対象（S̃_perfd）と降下の各項、Cor 8.14（A7）。
-/

@[expose] public section
noncomputable section
attribute [local instance] HasDerivedCategory.standard
universe u
open CategoryTheory SSet
open scoped Simplicial TensorProduct

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.DerivedCompletion SerrePositivity.EInfinity.Perfectoidization
open SerrePositivity.BhattScholze.PerfectoidizationInterface
open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ## G-A5-17：基底の perfectoid 拡大で Δ は変わらない -/

/-- R→R₁ から得る A_inf(R)→A_inf(R₁)。基底の剰余環上では指定した R 代数構造を誘導する。 -/
def perfectBaseHom (R₁ : Type u) [CommRing R₁] [Algebra R R₁] (h₁ : IsIntegralPerfectoid R₁ p) :
    OrientedPrism.Hom (perfectPrism p R hR) (perfectPrism p R₁ h₁) :=
  (_root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded (perfectPrism p R hR) (perfectPrism_isPerfect p R hR)
    (perfectPrism p R₁ h₁) (perfectPrism_bounded p R₁ h₁)
    ((perfectPrism_quotientEquiv p R₁ h₁).symm.toRingHom.comp
      ((algebraMap R R₁).comp (perfectPrism_quotientEquiv p R hR).toRingHom))).exists.choose

/-- 完備余接複体の台。A2 の cotangentWedge の i=1 を A/d≃R で読む。 -/
def completedCotangentUnderlying :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory (perfectPrismRing p R ⧸ (perfectPrism p R hR).ideal)) _⦋0⦌ :=
  let P := perfectPrism p R hR
  let q := (algebraMap R S).comp (perfectPrism_quotientEquiv p R hR).toRingHom
  let U := Under.mk (CommRingCat.ofHom q)
  (discreteToAnimated _ ≫ cotangentWedge P 1).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)

/-- 概要：perfectoid の射 R → R_1（完全 prism A → A_1）と R_1 代数 S について、比較写像 Δ_{S/A} → Δ_{S/A_1}：
(4) の Δ_{S/A} ⊗̂_A A_1 ≃ Δ_{(S ⊗̂_R R_1)/A_1}（A2-4 `derivedPrismaticCohomology_baseChange`）と乗法 S ⊗̂_R R_1 → S の関手性の合成。
方針：A2 の Kan 延長の自然変換。
規約：CAlg_A の射（終域は A_1 代数を A 代数とみなす）。
使われ方：`derivedPrismaticCohomology_baseIndep`。 -/
def baseComparison (R₁ : Type u) [CommRing R₁] [Algebra R R₁] [Algebra R₁ S] [IsScalarTower R R₁ S]
    (h₁ : IsIntegralPerfectoid R₁ p) :
    let res := cAlgRestrictScalars (E := E) (perfectBaseHom p R hR R₁ h₁).toRingHom
    (E.CAlg (perfectPrismRing p R)).Edge
      ((discreteDeltaFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S)))
      ((discreteDeltaFunctor (E := E) p R₁ h₁ ≫ res).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R₁ S))) := by
  let P := perfectPrism p R hR
  let P₁ := perfectPrism p R₁ h₁
  let a := perfectBaseHom p R hR R₁ h₁
  let res := cAlgRestrictScalars (E := E) a.toRingHom
  let x := (nerveMap (Under.map (CommRingCat.ofHom (perfectPrism_quotientEquiv p R hR).toRingHom)) ≫
    discreteToAnimated _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))
  let y := (nerveMap (Under.map (CommRingCat.ofHom (perfectPrism_quotientEquiv p R₁ h₁).toRingHom)) ≫
    discreteToAnimated _).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R₁ S))
  let xy := (animatedBaseChange P P₁ a).app _ x
  let H := derivedPrismaticCohomology (E := E) P₁ (hP := perfectPrism_bounded p R₁ h₁) ≫ completeCAlgInclusion (E := E) (p := p) P₁ ≫ res
  let m : SSet.Edge xy y := by
    sorry -- S⊗^L_R R₁→S は二つの指定された代数構造からの乗法。完備化は D32
  let first : SSet.Edge ((discreteDeltaFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))) (H.app _ xy) := by
    sorry -- A2 の derivedPrismaticCohomology_baseChange (4) で完備底変換の単位を移す
  let second := m.map H
  exact Classical.choose (show ∃ e : SSet.Edge ((discreteDeltaFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S)))
      (H.app _ y), Nonempty (first.toTruncated.CompStruct second.toTruncated e.toTruncated) from by
    sorry) -- 二辺の合成を表す三角形を選ぶ

include hR in
/-- 概要：perfectoid の間では L_{R_1/R} の p 完備化は零（ker θ の生成元が共通、L_{R/Z_p}^∧ = R[1] の遷移三角形）。
方針：既存の perfectoid の ker θ（`fontaineKernel_eq_span_image_distinguished`）と余接複体の一般論（A2-3 の `cotangentWedge` の隣）。
規約：導来 p 完備化。
使われ方：`derivedPrismaticCohomology_baseIndep`。 -/
theorem cotangent_perfectoid_vanish (R₁ : Type u) [CommRing R₁] [Algebra R R₁] (h₁ : IsIntegralPerfectoid R₁ p) :
    let k := perfectPrismRing p R ⧸ (perfectPrism p R hR).ideal
    CategoryTheory.Limits.IsZero ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence k).functor.obj
      ⟨completedCotangentUnderlying p R hR R₁⟩) := by
  sorry -- Fontaine 核の生成元を共通に取り、絶対完備余接複体の遷移三角形で相対項が消える

/-- 概要：G-A5-17：比較写像は同型。原典 Prop 7.10 の証明の「R を R⟨Y^{1/p^∞}⟩ に替えても余接複体は変わらず Δ も変わらない」。
方針：HT filtration と両立し gr^i で ∧^i L_{S/R} → ∧^i L_{S/R_1} を誘導（遷移三角形と `cotangent_perfectoid_vanish` で同型）⇒ Δ̄ で同型 ⇒
d 進 Nakayama（両者は導来 (p,d) 完備）で Δ で同型。完全化・mod d にも移る。
規約：—
使われ方：§3.4 (β)、Prop 7.10 の基底の移送（(ε)）。 -/
theorem derivedPrismaticCohomology_baseIndep (R₁ : Type u) [CommRing R₁] [Algebra R R₁]
    [Algebra R₁ S] [IsScalarTower R R₁ S] (h₁ : IsIntegralPerfectoid R₁ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (baseComparison (E := E) p R hR S R₁ h₁).toTruncated := by
  sorry -- 完備余接複体の遷移三角形から HT の各 gr が同値。d 完備性で指定比較辺に戻す

/-! ## 連結性と離散性 -/

/-- 概要：semiperfectoid（p 完備で perfectoid の商）。
方針：商の存在と p 完備性を分けて与え、R 線形な被覆は (α) で構成する。
規約：Prop。
使われ方：以下。 -/
abbrev IsSemiperfectoid (p : ℕ) [Fact p.Prime] (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  SerrePositivity.BhattScholze.IsSemiperfectoid p S

/-- 概要：G-A5-11：semiperfectoid S では L_{S/R}^∧[−1] が連結（S/p が semiperfect なので Ω^1_{(S/p)/F_p} = 0、L^∧ は**次数 −1 以下**。
「次数 −1 集中」や (I/I²)^∧[1] との同一視は qrsp/lci 型の別条件で、ここでは使わない。W9-II-14）。
方針：振幅の上界：perfectoid T → S 全射で L_{S/T}^∧ は次数 ≤ −1（H⁻¹ は (I/I²)^∧ の記述に使うだけ）、`cotangent_perfectoid_vanish`。
規約：導来 p 完備化、ホモロジー的連結性。
使われ方：`hodgeTate_connective_of_semiperfectoid`。 -/
theorem cotangent_shift_connective_of_semiperfectoid (hS : IsSemiperfectoid p R S) :
    Derived.IsConnectiveAt (perfectPrismRing p R ⧸ (perfectPrism p R hR).ideal) (-1)
      (completedCotangentUnderlying p R hR S) := by
  sorry -- H⁰ は mod p の微分の消滅と完備性から零。L^∧[-1] が連結となる上界のみ

/-- 概要：Δ̄_{S/A} は連結：HT filtration の gr^i = (∧^i L_{S/R})^∧[−i]{−i} が連結（G-A5-11）で、filtration は完備・網羅的（A2-3）。
方針：G-A5-10（gr が連結な完備 filtration の全体は連結）。
規約：—
使われ方：`prismaticPerfection_connective_of_semiperfectoid`。 -/
theorem hodgeTate_connective_of_semiperfectoid (hS : IsSemiperfectoid p R S) :
    Derived.IsConnectiveAt R 0 ((directHodgeTateFunctor (E := E) p R hR ≫ E.forget R).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))) := by
  sorry -- ∧ⁱ L^∧[-i] の連結性を HT filtration の各段から完備 filtered 余極限へ移す

/-- 概要：Δ_{S/A} は連結（Nakayama：d 完備で mod d が連結）、Δ_{S/A,perf} も連結（sequential 余極限と導来完備化は D^{≤0} を保つ、G-A5-10）。
方針：DerivedGeneral/Truncation の `derived_nakayama`。
規約：—
使われ方：離散性。 -/
theorem prismaticPerfection_connective_of_semiperfectoid (hS : IsSemiperfectoid p R S) :
    let A := perfectPrismRing p R
    Derived.IsConnectiveAt A 0 ((discreteDeltaFunctor (E := E) p R hR ≫ E.forget A).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ofAlgebra R S))) ∧
      Derived.IsConnectiveAt A 0 ((E.forget A).app _ (prismaticPerfection (E := E) p R hR S hS.1)) := by
  sorry -- d 進 Nakayama の後、正の係数制限の塔の余極限と (p,d) 完備化を取る

/-- 概要：Δ_{S/A,perf} は離散（連結かつ coconnective、Lemma 8.4 (a)）で、A4 の `prismaticPerfectionPrism` により完全 prism。
S_perfd = Δ_{S/A,perf}/d は離散な perfectoid 環（完全 prism の商、Thm 3.10）。
方針：連結性（上）で S_perfd が離散になることを示し、あとは A7-2 の芯 `perfectoidization_perfectPrism_of_discrete`・
`perfectoidization_isIntegralPerfectoid_of_discrete`（仮定は「S_perfd が離散」、G-A7-5、2026-11-02 の決定 4）に渡す。
規約：`IsTheoryDiscrete`（EInfinity/Perfectoidization/TheoryInterface）。
使われ方：以下、Cor 8.14。 -/
theorem perfectoidization_discrete_of_semiperfectoid (hS : IsSemiperfectoid p R S) :
    IsTheoryDiscrete (E := E) R (perfectoidization (E := E) p R hR S hS.1) := by
  sorry -- Δ_perf の連結性から mod d は連結。A4 Lemma 8.4(c) の coconnective 性と合わせる

theorem prismaticPerfection_discrete_of_semiperfectoid (hS : IsSemiperfectoid p R S) :
    IsTheoryDiscrete (E := E) (perfectPrismRing p R) (prismaticPerfection (E := E) p R hR S hS.1) :=
  prismaticPerfection_discrete_of_perfectoidization_discrete (E := E) p R hR S hS.1
    (perfectoidization_discrete_of_semiperfectoid (E := E) p R hR S hS)

theorem perfectoidization_isIntegralPerfectoid_of_semiperfectoid (hS : IsSemiperfectoid p R S) :
    IsIntegralPerfectoid (cAlgH0Algebra (E := E) R (perfectoidization (E := E) p R hR S hS.1)).right p :=
  perfectoidization_isIntegralPerfectoid_of_discrete (E := E) p R hR S hS.1
    (perfectoidization_discrete_of_semiperfectoid (E := E) p R hR S hS)

/-! ## Cor 7.3 の普遍 perfectoid 環との比較 -/

/-- 概要：R′：S の普遍 perfectoid 化（Cor 7.3、既存 `exists_perfectoidization_of_perfectoid_surjective_quotient` で選ぶ）。
方針：`IsPerfectoidization p (unit : S →+* R′)`。
規約：Type u。
使われ方：以下。 -/
theorem exists_universalPerfectoid (hS : IsSemiperfectoid p R S) :
    ∃ (C : Type u) (_ : CommRing C) (η : S →+* C), IsPerfectoidization p η := by
  obtain ⟨T, q, hT, hq⟩ := hS.2
  exact exists_perfectoidization_of_perfectoid_surjective_quotient hT q hq

def universalPerfectoidRing (hS : IsSemiperfectoid p R S) : Type u :=
  (exists_universalPerfectoid p R S hS).choose

instance (hS : IsSemiperfectoid p R S) : CommRing (universalPerfectoidRing p R S hS) :=
  (exists_universalPerfectoid p R S hS).choose_spec.choose

def universalPerfectoidUnit (hS : IsSemiperfectoid p R S) : S →+* universalPerfectoidRing p R S hS :=
  (exists_universalPerfectoid p R S hS).choose_spec.choose_spec.choose

theorem universalPerfectoidUnit_isPerfectoidization (hS : IsSemiperfectoid p R S) :
    IsPerfectoidization p (universalPerfectoidUnit p R S hS) :=
  (exists_universalPerfectoid p R S hS).choose_spec.choose_spec.choose_spec

/-- A4 の直接の単位を H⁰ に取る。A7 の普遍性には依存しない。 -/
abbrev directPerfdRing (U : A_R R) :=
  cAlgH0Algebra (E := E) R ((perfectoidizationFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))

def directPerfdRingUnit (U : A_R R) : U ⟶ directPerfdRing (E := E) p R hR U :=
  (discreteToH0 (E := E) R U).hom ≫ (cAlgH0OnHomotopy (E := E) R).map
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (directHodgeTateUnit (E := E) p R hR ≫ directToPerfection (E := E) p R hR) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U))

def directPerfdRingMap {U V : A_R R} (f : U ⟶ V) : directPerfdRing (E := E) p R hR U ⟶ directPerfdRing (E := E) p R hR V :=
  (cAlgH0OnHomotopy (E := E) R).map (SSet.Truncated.HomotopyCategory.homMk
    (((nerve.edgeMk f).map (perfectoidizationFunctor (E := E) p R hR)).toTruncated))

/-- Cor 7.3 で選んだ普遍標的を、S からの指定単位とともに切り落とし内に置く。 -/
def universalTarget (hS : IsSemiperfectoid p R S) :
    PerfUnderBounded p S (perfectSiteCutoff p R S) := by
  let η := universalPerfectoidUnit p R S hS
  let hη := universalPerfectoidUnit_isPerfectoidization p R S hS
  refine ⟨⟨Under.mk (CommRingCat.ofHom η), hη.1⟩, ?_⟩
  obtain ⟨T, q, hT, hq⟩ := hS.2
  have hs := surjective_of_isPerfectoidization_of_semiperfectoid_quotient hT q hq hS.1 η hη
  sorry -- Thm 7.4 の全射から #R′ ≤ #S ≤ κ

def universalTest (hS : IsSemiperfectoid p R S) : (perfectSite p R S hR)ᵒᵖ :=
  (perfectSiteEquivPerfectoidUnder p R hR S).inverse.obj (universalTarget p R S hS)

def universalTargetAlgebra (hS : IsSemiperfectoid p R S) : A_R R :=
  Under.mk (CommRingCat.ofHom ((universalPerfectoidUnit p R S hS).comp (algebraMap R S)))

/-- 完全試験 prism の d は正則。derived mod d を離散商 B/J として読む。 -/
def testModDResidueIso (U : (perfectSite p R S hR)ᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((modPrismFunctor (E := E) p R hR).app _ (testValue (E := E) p R hR S U))
      ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((targetAlgebra R p (ofAlgebra R S)).obj
        ((perfectResidueFunctor p R hR S).obj U).obj))) := by
  sorry -- B⊗^L_A A/d→B/J は d の正則性による商の標準同型。A/d≃R を通す

/-- mod d の標的を R′ に運ぶ射は、普遍標的における圏同値の counit。 -/
def universalTestModD (hS : IsSemiperfectoid p R S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((modPrismFunctor (E := E) p R hR).app _ (testValue (E := E) p R hR S (universalTest p R hR S hS)))
      ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (universalTargetAlgebra p R S hS))) := by
  let ε := (perfectSiteEquivPerfectoidUnder p R hR S).counitIso.app (universalTarget p R S hS)
  let forget : PerfUnderBounded p S (perfectSiteCutoff p R S) ⥤ A_R R :=
    (ObjectProperty.ι _) ⋙ targetAlgebra R p (ofAlgebra R S)
  exact testModDResidueIso (E := E) p R hR S (universalTest p R hR S hS) ≪≫
    (algebraNerveIso R (forget.mapIso ε)).map (E.discrete R)

/-- 概要：S_perfd → R′：比較写像の脚 Δ_{S/A,perf} → B_{R′}（A5-1 `perfectionComparisonLeg`（PerfectSite）、R′ の完全 prism）の mod d。S → S_perfd → R′ は単位。
方針：定義の展開。
規約：環準同型（両者は離散）。
使われ方：分裂全射。 -/
def perfectoidizationToUniversal (hS : IsSemiperfectoid p R S) :
    (directPerfdRing (E := E) p R hR (ofAlgebra R S)).right →+* universalPerfectoidRing p R S hS := by
  let B := universalTest p R hR S hS
  let leg := (perfectionComparisonLeg (E := E) p R hR S hS.1 B).1.map (modPrismFunctor (E := E) p R hR)
  let f := (perfectoidizationFunctor_vertex (E := E) p R hR S hS.1).hom ≫
    SSet.Truncated.HomotopyCategory.homMk leg.toTruncated ≫ (universalTestModD (E := E) p R hR S hS).hom
  exact ((cAlgH0OnHomotopy (E := E) R).map f ≫ (discreteToH0 (E := E) R (universalTargetAlgebra p R S hS)).inv).right.hom

/-- 概要：合成 S → S_perfd → R′ は全射（Thm 7.4、既存 `surjective_of_isPerfectoidization_of_semiperfectoid_quotient`）。R′ の普遍性で R′ → S_perfd があり
R′ → S_perfd → R′ = id、よって S_perfd → R′ は分裂全射。
方針：既存の全射性と `IsPerfectoidization` の一意性。
規約：—
使われ方：`perfectoidization_semiperfectoid_iso`。 -/
theorem perfectoidizationToUniversal_splitSurjective (hS : IsSemiperfectoid p R S) :
    let η := (directPerfdRingUnit (E := E) p R hR (ofAlgebra R S)).right.hom
    let q := universalPerfectoidUnit p R S hS
    let f := perfectoidizationToUniversal (E := E) p R hR S hS
    f.comp η = q ∧ Function.Surjective q ∧
      ∃ t : universalPerfectoidRing p R S hS →+* (directPerfdRing (E := E) p R hR (ofAlgebra R S)).right,
        t.comp q = η ∧ f.comp t = RingHom.id _ := by
  sorry -- 第0脚と HT 単位は S 上で両立。Thm 7.4 で q は全射。
        -- DiscreteCore で H⁰(S_perfd) は perfectoid。q の普遍性で t を得て f∘t=id

/-! ## S → S_perfd の全射性（原典 (4) の後半） -/

include hR in
/-- 概要：(α) perfectoid R_1 と全射 R_1 → S（R 代数）がある：R_1 = R ⊗̂ W(S^♭)（θ の全射性）または R⟨Y_k^{1/p^∞}⟩。
方針：既存の semiperfectoid の定義（perfectoid の商）からそのまま、または θ。
規約：R → R_1 は perfectoid の射（G-A5-17 が使える）。
使われ方：(β)。 -/
theorem exists_perfectoid_surjection (hS : IsSemiperfectoid p R S) :
    ∃ (R₁ : CommRingCat.{u}) (_ : Algebra R R₁) (q : R₁ →ₐ[R] S),
      IsIntegralPerfectoid R₁ p ∧ Function.Surjective q := by
  sorry -- hS の全射商から、完全基底との完備テンソルと θ で R 上の全射表示を作る

abbrev rootPolynomialFamily (J : Type u) :=
  AddMonoidAlgebra R (J →₀ Andre.powerRootExponentMonoid p (Fact.out : p.Prime).pos)

def rootVariable {J : Type u} (j : J) (n : ℕ) : rootPolynomialFamily p R J := by
  classical
  exact AddMonoidAlgebra.single (Finsupp.single j (Andre.powerRootVariableExponent p (Fact.out : p.Prime).pos n)) 1

abbrev rawRootQuotient (J : Type u) := rootPolynomialFamily p R J ⧸
  compatibleRootFamilyZeroIdeal (rootVariable p R (J := J))

def rootQuotientObj (J : Type u) : A_R R :=
  (completionFunctor p R).obj (ofAlgebra R (rawRootQuotient p R J))

def rootClass {J : Type u} (j : J) (n : ℕ) : (rootQuotientObj p R J).right :=
  (completionUnit p (CommRingCat.of (rawRootQuotient p R J))).hom
    (Ideal.Quotient.mk _ (rootVariable p R j n))

include hR in
/-- Thm 7.14 の拡大において核の生成元を同時に発根する。 -/
theorem exists_rootedBase {J : Type u} (f : J → R) :
    ∃ (T : CommRingCat.{u}) (_ : Algebra R T) (ρ : J → ℕ → T), IsIntegralPerfectoid T p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
      (∀ j, ρ j 0 = algebraMap R T (f j)) ∧ ∀ j n, ρ j (n+1)^p = ρ j n := by
  sorry -- Andre.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed と
        -- IsAbsolutelyIntegrallyClosed.exists_compatible_pow_roots を生成元ごとに適用

/-- π₁(L_{−/ℤ_p}/p) への射の全射性を、標準多項式表示のサイクルで読む。
mod p では L_{ℤ_p/ℤ} が消えるので ℤ を基底にできる。H⁻¹ には余接複体の
[−1,0] 切り捨てで足りる。その p 倍の cone で (a,b) の微分は p a + d b、
境界は (−d z,p z)。この記述は π₂ 以上の消滅を仮定しない。 -/
def surjectiveCotangentPiOneModP {V W : Type u} [CommRing V] [CommRing W] (f : V →+* W) : Prop :=
  letI := f.toAlgebra
  let P := Algebra.Generators.self ℤ V
  let Q := Algebra.Generators.self ℤ W
  let m := (Algebra.Generators.defaultHom P Q).toExtensionHom
  let d := P.toExtension.cotangentComplex
  let d' := Q.toExtension.cotangentComplex
  ∀ (a : Q.toExtension.CotangentSpace) (b : Q.toExtension.Cotangent),
    p • a + d' b = 0 →
    ∃ (x : P.toExtension.CotangentSpace) (y : P.toExtension.Cotangent) (z : Q.toExtension.Cotangent),
      p • x + d y = 0 ∧
        a - Algebra.Extension.CotangentSpace.map m x = -(d' z) ∧
        b - Algebra.Extension.Cotangent.map m y = p • z

/-- 概要：(β)(γ)：核の生成元 {f_j} ⊂ R_1 に Thm 7.14（André の補題で compatible roots を取る）で R_1 → R_1′（p 完備忠実平坦、perfectoid）を取り、
S′ := (R_1′⟨X_j^{1/p^∞}⟩/(X_j))^∧ → S ⊗̂_{R_1} R_1′ は π_0 と π_1(L_{−/Z_p}/p) で全射。HT 比較で H⁰(Δ̄_{S′}) → H⁰(Δ̄_{S ⊗̂ R_1′}) が全射、
完全化と Nakayama で S′_perfd → (S ⊗̂_{R_1} R_1′)_perfd が全射。基底は G-A5-17 で R_1′ に移す。
方針：A2-3 の HT filtration の H⁰ の記述（Fil_0 = S、gr^1 = L[−1]）。
規約：—
使われ方：`surjective_unit_of_semiperfectoid`。 -/
theorem rootQuotient_to_perfectoidization_surjective
    {R₁ S₀ : Type u} [CommRing R₁] [CommRing S₀] [Algebra R₁ R] [Algebra R₁ S₀]
    (h₁ : IsIntegralPerfectoid R₁ p) (hq : Function.Surjective (algebraMap R₁ S₀))
    (hc : IsModuleComplete S₀ (p : S₀) (ModuleCat.of S₀ S₀))
    (hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R₁)}) R)
    {J : Type u} (f : J → R₁) (hf : Ideal.span (Set.range f) = RingHom.ker (algebraMap R₁ S₀))
    (ρ : J → ℕ → R) (h₀ : ∀ j, ρ j 0 = algebraMap R₁ R (f j)) (hρ : ∀ j n, ρ j (n+1)^p = ρ j n) :
    let T := (completionFunctor p R).obj (ofAlgebra R (R ⊗[R₁] S₀))
    ∃ q : rootQuotientObj p R J ⟶ T,
      (∀ j n, q.right.hom (rootClass p R j n) = T.hom.hom (ρ j n)) ∧
      Function.Surjective q.right.hom ∧ surjectiveCotangentPiOneModP p q.right.hom ∧
      Function.Surjective ((cAlgH0OnHomotopy (E := E) R).map (SSet.Truncated.HomotopyCategory.homMk
        (((nerve.edgeMk q).map (directHodgeTateFunctor (E := E) p R hR)).toTruncated))).right.hom ∧
      Function.Surjective (directPerfdRingMap (E := E) p R hR q).right.hom := by
  sorry -- 根の評価は π₀ と π₁(L/ p) で全射。HT filtration、Frobenius 余極限と完備化で移す

/-- 概要：(δ) J を有限に帰着（S′ は有限部分集合の filtered 余極限、S′_perfd も、§3.2 の可換性）。
方針：A4 の `prismaticPerfection_filteredColimit`（W9-III-14 で A4/Perfectoidization へ）。
規約：—
使われ方：`surjective_unit_of_semiperfectoid`。 -/
def rootRename {I J : Type u} (f : I → J) : rawRootQuotient p R I →ₐ[R] rawRootQuotient p R J := by
  let a : rootPolynomialFamily p R I →ₐ[R] rootPolynomialFamily p R J :=
    AddMonoidAlgebra.mapDomainAlgHom R R (Finsupp.mapDomain.addMonoidHom f)
  exact Ideal.quotientMapₐ (R₁ := R)
    (I := compatibleRootFamilyZeroIdeal (rootVariable p R (J := I)))
    (J := compatibleRootFamilyZeroIdeal (rootVariable p R (J := J)))
    (f := a) (hIJ := by sorry) -- n=0 の各変数は f(i) の n=0 の変数に移り、商で零

def finiteRootDiagram (J : Type u) : Finset J ⥤ A_R R where
  obj I := ofAlgebra R (rawRootQuotient p R I)
  map {I I'} h := Under.homMk (CommRingCat.ofHom (rootRename p R (Set.inclusion (leOfHom h))).toRingHom)
    (by sorry) -- 係数は固定
  map_id := by sorry -- 変数名の恒等写像
  map_comp := by sorry -- 変数名の包含の合成

def finiteRootCocone (J : Type u) : Limits.Cocone (finiteRootDiagram p R J) where
  pt := ofAlgebra R (rawRootQuotient p R J)
  ι := { app := fun I => Under.homMk (CommRingCat.ofHom (rootRename p R (Subtype.val : I → J)).toRingHom)
           (by sorry) -- 係数は固定
         naturality := by sorry } -- 全体 J への同じ包含

abbrev rootIndexShape (J : Type u) : SSet.{u+1} :=
  (SSet.uliftFunctor.{u+1,u}).obj (nerve (Finset J))

def finiteRootNerve (J : Type u) : rootIndexShape J ⟶ algebraNerve R where
  app _ := ↾fun x => ((finiteRootDiagram p R J).mapComposableArrows _).obj x.down
  naturality := by sorry -- 各合成可能列を写した nerve の自然性

def finiteRootJoinCocone (J : Type u) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (finiteRootNerve p R J) := by
  let c := finiteRootCocone p R J
  exact Classical.choose (show ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (finiteRootNerve p R J),
    d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c.pt ∧ ∀ I : Finset J,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg d (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex I))).edge =
        (nerve.edgeMk (c.ι.app I)).edge from by
    sorry) -- 同じ包含の余錐を nerve に送る

/-- 完備 R 代数の圏で mod d を取る。値の台は A4 の modPrismFunctor。 -/
def rootPerfdFunctor :
    algebraNerve R ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (E.CAlg R) (fun x =>
      isPCompleteVertex p R ((E.forget R).app _ x)) : SSet.{u+1}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (perfectoidizationFunctor (E := E) p R hR) (by
    sorry) -- (p,d) 完備な Δ_perf の mod d は p 完備

theorem rootQuotient_finite_reduction (J : Type u) :
    Nonempty (Limits.IsColimit (finiteRootCocone p R J)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (rootPerfdFunctor (E := E) p R hR) (finiteRootJoinCocone p R J)) ∧
      ((∀ I : Finset J, Function.Surjective
        (directPerfdRingUnit (E := E) p R hR (rootQuotientObj p R I)).right.hom) →
        Function.Surjective (directPerfdRingUnit (E := E) p R hR (rootQuotientObj p R J)).right.hom) := by
  sorry -- 単項式・関係は有限個の変数を使う。A4 の prismaticPerfection_filteredColimit と
        -- mod d で完備余極限を取り、連結性のもとで完備化単位に沿って H⁰ の全射を移す

/-- 概要：(ε) Prop 7.10（A3-4 `rootQuotient_prismatic_perfection_eq`）：J 有限で S′_perfd = R_1′⟨X^{1/p^∞}⟩/(X^{1/p^∞}) かつ S′ → S′_perfd 全射。
基底が R なら G-A5-17 で R_1′ へ。
方針：A3-4。
規約：—
使われ方：`surjective_unit_of_semiperfectoid`。 -/
theorem rootQuotient_unit_surjective (J : Type u) [Finite J] :
    let U := rootQuotientObj p R J
    let Q := (completionFunctor p R).obj (ofAlgebra R
      (rootPolynomialFamily p R J ⧸ compatibleRootFamilyIdeal (rootVariable p R (J := J))))
    Function.Surjective (directPerfdRingUnit (E := E) p R hR U).right.hom ∧
      ∃ e : directPerfdRing (E := E) p R hR U ≅ Q, ∀ j n,
        (directPerfdRingUnit (E := E) p R hR U ≫ e.hom).right.hom (rootClass p R j n) = 0 := by
  sorry -- Prop 7.10 の有限変数模型を G-A5-17 で基底移送し、全段の根を殺す指定商と比較

/-- 概要：S → S_perfd は全射（(α)〜(ζ)、忠実平坦な R_1 → R_1′ で全射性を反映）。
方針：上の四つ。
規約：—
使われ方：`perfectoidization_semiperfectoid_iso`。 -/
theorem surjective_unit_of_semiperfectoid (hS : IsSemiperfectoid p R S) :
    Function.Surjective (directPerfdRingUnit (E := E) p R hR (ofAlgebra R S)).right.hom := by
  sorry -- (α) の R 上の表示、G-A5-17、Thm 7.14、根の評価、有限近似、Prop 7.10。
        -- p 完備忠実平坦な底変換で元の単位の全射性を反映する

/-- 概要：Prop 8.5 の系 3：S_perfd ≅ R′（S の下で）。分裂全射 S_perfd → R′ と、S → S_perfd 全射 ⇒ R′ → S_perfd 全射で分裂単射 ⇒ 同型。
方針：上の二つ。A5-1 の `perfectoidization_semiperfectoid` の証明。
規約：環の同型と `VertexIso`。
使われ方：A5-4（S̃_perfd と Δ_{S̃,perf}/d の同一視）、Cor 8.14。 -/
theorem perfectoidization_semiperfectoid_iso (hS : IsSemiperfectoid p R S) :
    let U := ofAlgebra R S
    ∃ e : (directPerfdRing (E := E) p R hR U).right ≃+* universalPerfectoidRing p R S hS,
      e.toRingHom = perfectoidizationToUniversal (E := E) p R hR S hS ∧
      e.toRingHom.comp (directPerfdRingUnit (E := E) p R hR U).right.hom = universalPerfectoidUnit p R S hS ∧
      ∃ v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (perfectoidization (E := E) p R hR S hS.1)
          ((E.discrete R).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (universalTargetAlgebra p R S hS))),
        ((cAlgH0OnHomotopy (E := E) R).map ((perfectoidizationFunctor_vertex (E := E) p R hR S hS.1).hom ≫ v.hom) ≫
          (discreteToH0 (E := E) R (universalTargetAlgebra p R S hS)).inv).right.hom = e.toRingHom := by
  sorry -- 分裂の t は S→H⁰(S_perfd) の全射性で全射、かつ分裂単射。
        -- 逆同型の指定単位との等式を保ち、離散な両環を CAlg_R に移す

end SerrePositivity.BhattScholze.Perfectoidization.Derived
