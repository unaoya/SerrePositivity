-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Construction.Definition（仮。原典 Not 8.1、Def 8.2、Example 8.3、Lemma 8.4）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md §2.1・§2.2・§2.4、単位 A4-1・A4-2・A4-4。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Semiperfectoid.AinfClassicalMaps

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeVertexTriangles
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import Mathlib.Algebra.Category.Ring.Basic
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
-- 本ファイルは drafts/DerivedGeneral/ScalarRestriction.lean の cAlgRestrictScalars と忘却比較（M13）も使う。
-- 本ファイルは drafts/A2/{DerivedPrismaticCohomology,HodgeTateFiltration,BaseChangeAndTensor}.lean、drafts/A3/DiscreteCase.lean、
-- drafts/DerivedGeneral/{Truncation,CompletionFunctor}.lean、drafts/Sheaves/CAlgValued.lean、drafts/Shared/EInfinityPowerOperation.lean を import する。

/-!
# perfectoid 化の定義と coconnectivity（BS 著者版 Not 8.1、Def 8.2、Example 8.3、Lemma 8.4）

## 概要
perfectoid 環 R に対応する完全 prism (A,(d))（Not 8.1）の上で、導来 p 完備な R 代数 S について、Δ_{S/A,perf} := (colim_φ Δ_{S/A})^∧
（Frobenius 余極限の (p,d) 完備化、Def 8.2 (1)）と S_perfd := Δ_perf ⊗^L_A A/d（Def 8.2 (2)）を定義する。Lemma 8.4：両者は D^{≥0}。
その過程で H⁰(Δ_perf) は p 完備な完全 δ 環で d は正則、(H⁰(Δ_perf), (d)) は完全 prism。Example 8.3：標数 p では S_perfd は通常の完全化。

## 方針
A2 の Δ（CAlg_A 値）と φ_A 半線形な Frobenius φ : Δ → φ_{A*}Δ から、原典どおりの塔 Δ → φ_{A*}Δ → φ_{A*}²Δ → ⋯（遷移射 φ_{A*}^n(φ)、W9-II-01 で訂正）
の CAlg_A の余極限を取って完備化（DerivedGeneral/CompletionFunctor）。Lemma 8.4 (a) は E∞-F_p 代数の P⁰（Shared/EInfinityPowerOperation、coherent な
自然変換）：Δ_perf/p では塔の shift が P⁰ と同じ作用を誘導し可逆、P⁰ は正次数のホモトピーを殺す。(b) は H⁰ の単射 C/p ↪ H⁰(X/p) と一般の Rem 2.2
（G-A4-8 = G-A3-6）、(c) は Lemma 2.34。

## 規約
定義域は原典どおり導来 p 完備な S（D41）。**A7（D60）**：原典の定義域は導来 p 完備な animated R 代数で、本ファイルの離散版は
drafts/A7/AnimatedPerfectoidization.lean の `perfectoidizationAnimated` の `discreteToAnimated` に沿う制限（`perfectoidizationAnimated_discrete`）。非完備な離散 S への延長は界面の欄（drafts/A4/InterfaceFields）。値は CAlg_A・CAlg_R を正（D35）。
塔は原典どおり φ_{A*}^n（スカラー制限の正の反復。D42 は撤回：Res_φ ≃ (φ^{-1})^* であって φ^* ではない）。

## 使われ方
E3 の `perfd`（InterfaceFields）、Prop 8.5（A5）、Prop 8.10〜Cor 8.12（A6）、Prop 8.13・Cor 8.14（A7）、Thm 10.11（A8）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity
open SerrePositivity.BhattScholze.PerfectoidizationInterface

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-! ## Not 8.1：perfectoid 環と完全 prism -/

/-- BS 著者版 Notation 8.1 の A_inf(R)。
本体の固定した二分岐（零環ではR、それ以外ではW(R♭)）をそのまま使う。 -/
abbrev perfectPrismCoefficients : CommRingCat.{u} :=
  Semiperfectoid.ainfClassicalCoefficients p R

/-- Notation 8.1 の係数環の台。 -/
abbrev perfectPrismRing : Type u := (perfectPrismCoefficients p R : Type u)

/-- Notation 8.1 の固定した Fontaine 射。本体の構成を使う。 -/
abbrev perfectPrismTheta (hR : IsIntegralPerfectoid R p) : perfectPrismRing p R →+* R :=
  Semiperfectoid.ainfClassicalTheta p R hR

/-- Notation 8.1 の標準 δ 構造。零環の枝も本体で処理済み。 -/
abbrev perfectPrismDelta (hR : IsIntegralPerfectoid R p) : DeltaStructure p (perfectPrismRing p R) :=
  Semiperfectoid.ainfClassicalDelta p R hR

/-- BS 著者版 Notation 8.1 の prism。
本体のTheorem 3.10の表示を固定したFontaine係数へ移した構成を使う。
P⁰の演算やその法則はこの選択に使わない。 -/
abbrev perfectPrism (hR : IsIntegralPerfectoid R p := by assumption) :
    OrientedPrism p (perfectPrismRing p R) := Semiperfectoid.ainfClassicalPrism p R hR

/-- Notation 8.1 の選択した prism は完全。 -/
theorem perfectPrism_isPerfect (hR : IsIntegralPerfectoid R p) :
    (perfectPrism p R hR).deltaStructure.IsPerfect := Semiperfectoid.ainfClassicalPrism_perfect p R hR

/-- Notation 8.1 の選択した prism は有界。 -/
theorem perfectPrism_bounded (hR : IsIntegralPerfectoid R p) : IsBoundedPrism (perfectPrism p R hR) :=
  Semiperfectoid.ainfClassicalPrism_bounded p R hR

/-- Notation 8.1 の剰余環とRの指定された同型。固定θを通す本体の同型を使う。 -/
abbrev perfectPrism_quotientEquiv (hR : IsIntegralPerfectoid R p) :
    (perfectPrismRing p R ⧸ (perfectPrism p R hR).ideal) ≃+* R :=
  Semiperfectoid.ainfClassicalResidueEquiv p R hR

/-- Notation 8.1 の固定θ・δと両立する完全 prism の存在。
Theorem 3.10から得た本体のprismを取り、剰余同型の単射性でθの核を同定する。 -/
theorem exists_perfectPrismOverTheta (hR : IsIntegralPerfectoid R p) :
    ∃ P : OrientedPrism p (perfectPrismRing p R),
      P.deltaStructure.IsPerfect ∧ P.deltaStructure = perfectPrismDelta p R hR ∧
        P.ideal = RingHom.ker (perfectPrismTheta p R hR) := by
  refine ⟨perfectPrism p R hR, perfectPrism_isPerfect p R hR,
    Semiperfectoid.ainfClassicalPrism_delta p R hR, ?_⟩
  change _ = RingHom.ker (Semiperfectoid.ainfClassicalTheta p R hR)
  rw [← Semiperfectoid.ainfClassicalResidueEquiv_theta p R hR,
    RingHom.ker_comp_of_injective _ (Semiperfectoid.ainfClassicalResidueEquiv p R hR).injective,
    Ideal.mk_ker]

/-! ## Def 8.2 -/


/-- F の正方向の n 回合成。第 n 遷移は辺 φ にこの関手を適用したもの。 -/
def iterateRestriction {E : SSet.{u+1}} (F : E ⟶ E) (n : ℕ) : E ⟶ E :=
  match n with
  | 0 => 𝟙 E
  | j + 1 => F ≫ iterateRestriction F j

abbrev frobeniusTowerShape : SSet.{u+1} := (SSet.uliftFunctor.{u+1, 0}).obj (nerve ℕ)

/-- 余極限を取る図式は、頂点列だけでなくすべての後続辺を指定して選ぶ。 -/
def restrictionSequence {E : SSet.{u+1}} [Quasicategory E] (F : E ⟶ E)
    {x : E _⦋0⦌} (φ : SSet.Edge x (F.app _ x)) : frobeniusTowerShape.{u} ⟶ E :=
  Classical.choose (show ∃ D : frobeniusTowerShape.{u} ⟶ E,
    (∀ n : ℕ, D.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex n)) = (iterateRestriction F n).app _ x) ∧
    (∀ n : ℕ, D.app (Opposite.op ⦋1⦌) (ULift.up (ComposableArrows.mk₁ (homOfLE (Nat.le_succ n)))) =
      (φ.map (iterateRestriction F n)).edge) from by
    sorry) -- 後続辺の列を ℕ の nerve に延長し、高次の合成を一貫して選ぶ

abbrev completeCAlgInclusion {A : Type u} [CommRing A] (P : OrientedPrism p A) :
    CompleteCAlg (E := E) P ⟶ E.CAlg A :=
  _root_.SerrePositivity.BhattScholze.Prismatic.prismCompleteInclusion (E := E) P

/-- A2 の完備代数値の Δ を全 CAlg に含め、A/d≃R で係数を同定する。 -/
def discreteDeltaFunctor (hR : IsIntegralPerfectoid R p) :
    algebraNerve R ⟶ E.CAlg (perfectPrismRing p R) := by
  let P := perfectPrism p R hR
  let change := Under.map (CommRingCat.ofHom (perfectPrism_quotientEquiv p R hR).toRingHom)
  exact nerveMap change ≫ derivedPrismaticCohomologyDiscrete (E := E) P (hP := perfectPrism_bounded p R hR) ≫ completeCAlgInclusion (E := E) (p := p) P

/-- A2 の derivedPrismaticFrobenius（drafts/A2/DerivedPrismaticCohomology.lean）の離散 U 成分。
A2 の結論がまだ True なので A4 に仮置きし、BS-D4 で本来の自然変換の成分に置き換える。 -/
def discreteDeltaFrobenius (hR : IsIntegralPerfectoid R p) (U : A_R R) :
    let x := (discreteDeltaFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)
    SSet.Edge x ((cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift).app _ x) := by
  sorry -- A2 待ち：derivedPrismaticFrobenius を離散 U で評価し、完備部分圏の包含で送る

def directTower (hR : IsIntegralPerfectoid R p) (U : A_R R) :
    frobeniusTowerShape.{u} ⟶ E.CAlg (perfectPrismRing p R) :=
  restrictionSequence (cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift)
    (discreteDeltaFrobenius (E := E) p R hR U)

/-- 概要：Frobenius の sequential 図式 Δ_S → φ_{A*}Δ_S → φ_{A*}²Δ_S → ⋯（CAlg_A の ℕ 添字の図式、遷移射は φ_{A*}^n(φ)。原典 Def 8.2 (1) の形、W9-II-01）。
方針：A2 の `derivedPrismaticFrobenius` φ : Δ → φ_{A*}Δ と、スカラー制限 φ_{A*} = Res_{φ_A} の反復（G-A4-3）。φ_{A*} の逆は使わない。
規約：A 完全は余極限の shift が φ_A 半線形な自己同型になることにだけ使う。
使われ方：Δ_perf の余極限。 -/
def frobeniusTower (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    frobeniusTowerShape.{u} ⟶ E.CAlg (perfectPrismRing p R) :=
  directTower (E := E) p R hR (Under.mk (CommRingCat.ofHom (algebraMap R S)))

/-- (p,d) 完備 CAlg への反射の後に包含する関手（G-A2-3）。 -/
abbrev reflectCompleteCAlg {A : Type u} [CommRing A] (P : OrientedPrism p A) : E.CAlg A ⟶ CompleteCAlg (E := E) P :=
  _root_.SerrePositivity.BhattScholze.Prismatic.prismCompletion (E := E) P

def prismCAlgCompletion {A : Type u} [CommRing A] (P : OrientedPrism p A) : E.CAlg A ⟶ E.CAlg A :=
  reflectCompleteCAlg (E := E) (p := p) P ≫ completeCAlgInclusion (E := E) (p := p) P

def prismCAlgCompletionUnit {A : Type u} [CommRing A] (P : OrientedPrism p A) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (E.CAlg A)) (prismCAlgCompletion (E := E) (p := p) P) :=
  _root_.SerrePositivity.BhattScholze.Prismatic.prismCompletionUnit (E := E) P

/-- A→A/d≃R に沿う導来テンソル。係数制限の左随伴（G-A4-4）。 -/
def modPrismFunctor (hR : IsIntegralPerfectoid R p) : E.CAlg (perfectPrismRing p R) ⟶ E.CAlg R := by
  sorry -- 要確認：perfectPrismTheta 沿いの CAlg 底変換の実装名

def modPrismAdjunction (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (modPrismFunctor (E := E) p R hR) (cAlgRestrictScalars (E := E) (perfectPrismTheta p R hR)) := by
  sorry -- A→A/d≃R に沿う係数拡大と制限の随伴

def directTowerColimit (hR : IsIntegralPerfectoid R p) (U : A_R R) :
    { c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (directTower (E := E) p R hR U) // _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c } := by
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (directTower (E := E) p R hR U) := by
    sorry -- G-A4-2 の CAlg の sequential 余極限
  exact ⟨hc.choose, hc.choose_spec⟩

def directPerfectionValue (hR : IsIntegralPerfectoid R p) (U : A_R R) : (E.CAlg (perfectPrismRing p R)) _⦋0⦌ :=
  (prismCAlgCompletion (E := E) (p := p) (perfectPrism p R hR)).app _ (directTowerColimit (E := E) p R hR U).val.vertex

/-- Δ_U から完備化した余極限への射を、第0脚と反射の単位で指定する。 -/
def directPerfectionLeg (hR : IsIntegralPerfectoid R p) (U : A_R R) :
    (HomotopyCategory.mk ((discreteDeltaFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) :
      hoFunctor.obj (E.CAlg (perfectPrismRing p R))) ⟶ HomotopyCategory.mk (directPerfectionValue (E := E) p R hR U) := by
  let c := (directTowerColimit (E := E) p R hR U).val
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (0 : ℕ)))
  exact eqToHom (by sorry) ≫ -- restrictionSequence の第0頂点は Δ_U
    SSet.Truncated.HomotopyCategory.homMk l.toTruncated ≫
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (prismCAlgCompletionUnit (E := E) (p := p) (perfectPrism p R hR)) c.vertex

/-- 概要：Def 8.2 (1)：Δ_{S/A,perf} := (colim_φ Δ_{S/A})^∧（CAlg_A の余極限の (p,d) 完備化）。
方針：G-A4-2（CAlg_A の sequential 余極限）と G-A2-3（完備化の反射）。
規約：(p,d) 完備な E∞-A 代数。φ_S が誘導する自己同型をもつ。
使われ方：S_perfd、Lemma 8.4、Prop 8.5。 -/
def prismaticPerfection (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    (E.CAlg (perfectPrismRing p R)) _⦋0⦌ :=
  directPerfectionValue (E := E) p R hR (Under.mk (CommRingCat.ofHom (algebraMap R S)))

/-- 完全基底では φ_A が同型なので、制限は塔の余極限を保つ。 -/
theorem restrictFrobeniusTowerColimit (hR : IsIntegralPerfectoid R p) (U : A_R R)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (directTower (E := E) p R hR U)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift) c) := by
  sorry -- 要確認：ScalarRestriction へ。同型に沿う制限と逆の制限は comp・id で互いに逆

def restrictFrobeniusCompletion (hR : IsIntegralPerfectoid R p) :
    let P := perfectPrism p R hR
    let res := cAlgRestrictScalars (E := E) P.deltaStructure.frobeniusLift
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (prismCAlgCompletion (E := E) (p := p) P ≫ res) (res ≫ prismCAlgCompletion (E := E) (p := p) P) := by
  sorry -- 要確認：ScalarRestriction へ。(p,d) と (p,φ(d)) は同じ完備性を定める

/-- 概要：Δ_perf 上の φ_A 半線形な自己同型（余極限の shift）。
方針：sequential 図式の shift。
規約：—
使われ方：Lemma 8.4 (b)、完全 δ 構造。 -/
def prismaticPerfectionFrobenius (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let x := prismaticPerfection (E := E) p R hR S hS
    { e : SSet.Edge x ((cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift).app _ x) //
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated } := by
  sorry -- 塔の第0項を落とす shift は cofinal。φ_A が自己同型なので制限が余極限と完備化に両立

theorem prismaticPerfectionFrobenius_leg (hR : IsIntegralPerfectoid R p) (S : Type u)
    [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let U := ofAlgebra R S
    let F := cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift
    let l := directPerfectionLeg (E := E) p R hR U
    l ≫ SSet.Truncated.HomotopyCategory.homMk (prismaticPerfectionFrobenius (E := E) p R hR S hS).val.toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (discreteDeltaFrobenius (E := E) p R hR U).toTruncated ≫
        (hoFunctor.map F).toFunctor.map l := by
  sorry -- 余錐の shift の第0脚の式と完備化単位の自然性

/-- 概要：Def 8.2 (2)：S_perfd := Δ_perf ⊗^L_A A/d（CAlg_R の対象）。
方針：底変換 CAlg_A → CAlg_R（G-A4-4）。
規約：p 完備な E∞-S 代数（S → S_perfd は InterfaceFields の単位）。
使われ方：E3 の `perfd`。 -/
def perfectoidization (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    (E.CAlg R) _⦋0⦌ := (modPrismFunctor (E := E) p R hR).app _ (prismaticPerfection (E := E) p R hR S hS)

/-- 概要：D(R) 値の S_perfd（忘却）。
方針：`cAlgForgetDerived R`。
規約：E3 の D(R) 版 `perfd` の値。
使われ方：`nonempty_e3_of_theory` 経由の D(R) 版。 -/
def perfectoidizationDerived (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌ := (E.forget R).app _ (perfectoidization (E := E) p R hR S hS)

/-- 界面の π₀ から H⁰ の環と構造射を取る。 -/
def cAlgH0Algebra (A : Type u) [CommRing A] (x : (E.CAlg A) _⦋0⦌) : A_R A := (E.pi0 A).obj (SSet.HomotopyCategory.mk x)

/-- H⁰ は代数の擬同型を同型に送り、CAlg のホモトピー圏を経由する。 -/
def cAlgH0OnHomotopy (A : Type u) [CommRing A] : (E.CAlg A).HomotopyCategory ⥤ A_R A :=
  E.pi0 A

/-- Res_f は H⁰ の環の台を保ち、その A 作用を f に沿って読む。 -/
def restrictH0Equiv {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (x : (E.CAlg B) _⦋0⦌) :
    (cAlgH0Algebra (E := E) A ((cAlgRestrictScalars (E := E) f).app _ x)).right ≃+* (cAlgH0Algebra (E := E) B x).right := by
  exact cAlgRestrictScalars_h0 (E := E) f x

theorem restrictH0Equiv_base {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (x : (E.CAlg B) _⦋0⦌) :
    (restrictH0Equiv (E := E) f x).toRingHom.comp (cAlgH0Algebra (E := E) A ((cAlgRestrictScalars (E := E) f).app _ x)).hom.hom =
      (cAlgH0Algebra (E := E) B x).hom.hom.comp f := by
  sorry -- 忘却後の係数作用が f との合成であること

def shiftOnH0 {A : Type u} [CommRing A] (f : A →+* A) (x : (E.CAlg A) _⦋0⦌)
    (e : SSet.Edge x ((cAlgRestrictScalars (E := E) f).app _ x)) :
    (cAlgH0Algebra (E := E) A x).right →+* (cAlgH0Algebra (E := E) A x).right :=
  (restrictH0Equiv (E := E) f x).toRingHom.comp
    ((cAlgH0OnHomotopy (E := E) A).map (SSet.HomotopyCategory.homMk e)).right.hom

/-! ## Lemma 8.4 -/

/-- 概要：Lemma 8.4 (a)：Δ_perf ∈ D^{≥0}。
方針：Δ_perf/p は E∞-F_p 代数で、φ の自己同型が P⁰ を誘導し P⁰ が可逆（Shared/EInfinityPowerOperation の levelwise Frobenius ＝ P⁰）、
P⁰ は π_n（n > 0）で零（Rem 2.2.7）⇒ π_n(Δ_perf/p) = 0 ⇒ Δ_perf/p ∈ D^{≥0} ⇒ Δ_perf ∈ D^{≥0}（p 完備、導来 Nakayama）。
規約：D(A) の `IsCoconnectiveAt 0`（cohomological な D^{≥0}。W9-I-28 で名前を原典に揃えた）。
使われ方：(b)、Cor 8.14、Prop 8.5、Thm 10.11。 -/
theorem prismaticPerfection_coconnective (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let A := perfectPrismRing p R
    InfinityCategories.Derived.IsCoconnectiveAt A 0
      ((E.forget A).app _ (prismaticPerfection (E := E) p R hR S hS)) := by
  have hforget := cAlgRestrictScalars_forget (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift
  sorry -- D79 改訂：mod p を界面の素体 EInfinityPrimeField p へ係数制限する。
  -- ho(CAlg) 上の全整数次数の P⁰ は shift と同じ作用で可逆、正の π では零。
  -- E.restrictD_homologyIso で H^{−n} の消滅へ戻し、p 完備性と導来 Nakayama。
  -- 二重模型の実現上の Frobenius 比較は A4 の局所補題で、G10 の後に示す。
  -- coherent な Sp 値の持ち上げは使わない。

/-- 概要：Lemma 8.4 (b)：H⁰(Δ_perf) は p ねじれなしで、φ は mod p で Frobenius、よって p 完備な完全 δ 環（A → H⁰ は δ 射）。
方針（W9-II-04）：X := Δ_perf、C := H⁰ X。長完全列から C[p] = H^{−1}(X/p) = 0 と単射 C/p ↪ H⁰(X/p)（同型ではない）。φ の自然性と P⁰ が H⁰(X/p) で p 乗
であることから φ(c) ≡ c^p mod p、一般の p ねじれなし環の Rem 2.2（G-A4-8 = G-A3-6。A3 の `deltaStructure_of_discrete_pTorsionFree` は `IsDiscretePrismatic` を
仮定するので使わない）で δ、A → C は δ 射（p 消去）、φ 全単射で `DeltaStructure.IsPerfect`、p 完備性は X の導来完備性と p ねじれなしから。X の離散性は使わない。
規約：—
使われ方：(c)、Cor 8.14。 -/
theorem prismaticPerfection_h0_perfectDelta (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let P := perfectPrism p R hR
    let x := prismaticPerfection (E := E) p R hR S hS
    let C := cAlgH0Algebra (E := E) (perfectPrismRing p R) x
    let F := shiftOnH0 (E := E) P.deltaStructure.frobeniusLift x (prismaticPerfectionFrobenius (E := E) p R hR S hS).val
    Function.Injective (fun c : C.right => (p : C.right) * c) ∧
      IsAdicComplete (Ideal.span {(p : C.right)}) C.right ∧
      ∃ D : DeltaStructure p C.right, D.IsPerfect ∧ D.frobeniusLift = F ∧
        P.deltaStructure.IsDeltaHom D C.hom.hom := by
  sorry -- C[p] = 0、C/p ↪ H⁰(X/p) で shift が p 乗に一致するので (F(c)−c^p)/p が一意。
        -- 基底との可換性は p を消去し、完全性は shift の可逆性から

/-- 概要：Lemma 8.4 (c)：d は H⁰(Δ_perf) で正則（Lemma 2.34：完全 p 完備 δ 環の distinguished 元）、よって S_perfd ∈ D^{≥0}
（H^{−1}(Δ_perf ⊗^L A/d) = H⁰(Δ_perf)[d] = 0）。
方針：`DeltaStructure.IsPerfect.distinguished_mul_injective`（Lemma 2.34）。
規約：—
使われ方：Cor 8.14、Prop 8.5。 -/
theorem perfectoidization_coconnective (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let C := cAlgH0Algebra (E := E) (perfectPrismRing p R) (prismaticPerfection (E := E) p R hR S hS)
    IsLeftRegular (C.hom.hom (perfectPrism p R hR).generator) ∧
      InfinityCategories.Derived.IsCoconnectiveAt R 0 (perfectoidizationDerived (E := E) p R hR S hS) := by
  sorry -- Lemma 2.34 と (b) で d は正則。d の cofiber の H⁻¹ は C[d] = 0

/-- 概要：(H⁰(Δ_perf), (d)) は完全 prism（(b)(c) から直接。A3 の (2) は Δ・Δ̄ の離散性を仮定するので使わない、W9-II-04）。
方針：H⁰ の導来 (p,d) 完備性、(b) の δ 構造、基底から来る p ∈ (d, φ(d))、Lemma 2.34 の d 正則性、完全性。
規約：`OrientedPrism`。
使われ方：Cor 8.14（S_perfd 離散なら perfectoid 環）、Prop 8.5。 -/
def prismaticPerfectionPrism (hR : IsIntegralPerfectoid R p) (S : Type u) [CommRing S] [Algebra R S]
    (hS : SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    let A := perfectPrismRing p R
    let P := perfectPrism p R hR
    let x := prismaticPerfection (E := E) p R hR S hS
    let C := cAlgH0Algebra (E := E) A x
    { Q : OrientedPrism p C.right // Q.generator = C.hom.hom P.generator ∧ Q.deltaStructure.IsPerfect ∧
      P.deltaStructure.IsDeltaHom Q.deltaStructure C.hom.hom ∧
      Q.deltaStructure.frobeniusLift = shiftOnH0 (E := E) P.deltaStructure.frobeniusLift x
        (prismaticPerfectionFrobenius (E := E) p R hR S hS).val } := by
  sorry -- (b) の δ と (c) の正則性、C の導来 (p,d) 完備性、基底の p_mem

/-! ## filtered 余極限との可換性（原典 Prop 8.5 の証明 (2) の左辺。W9-III-14 で A4 へ） -/

/-- 全ての離散 S に塔・余極限・完備化を関手の段で施す（Def 8.2 の入力では S は p 完備）。 -/
def completePerfectionFunctor (hR : IsIntegralPerfectoid R p) :
    algebraNerve R ⟶ CompleteCAlg (E := E) (perfectPrism p R hR) := by
  sorry -- A2 の Frobenius 自然変換の塔を関手圏で作り、点ごとの余極限に reflectCompleteCAlg を施す

def directPerfectionFunctor (hR : IsIntegralPerfectoid R p) : algebraNerve R ⟶ E.CAlg (perfectPrismRing p R) :=
  completePerfectionFunctor (E := E) p R hR ≫ completeCAlgInclusion (E := E) (p := p) (perfectPrism p R hR)

def directPerfectionVertex (hR : IsIntegralPerfectoid R p) (U : A_R R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((directPerfectionFunctor (E := E) p R hR).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex U)) (directPerfectionValue (E := E) p R hR U) := by
  sorry -- 同じ塔を評価した余極限余錐の比較と完備化の関手性

/-- 概要：左辺：S ↦ Δ_{S/A,perf} は（完備化した）filtered 余極限と可換（Δ は sifted 余極限を保つ、colim_φ と完備化も）。
方針：A2-4 `derivedPrismaticCohomology_siftedColimit`、Frobenius 塔の余極限（G-A4-2）、完備化の反射性（G-A2-3）だけ——完備圏で二つの余極限を交換する。
site の Tot・StrongDescent は不要なので A4 に置く（W9-III-14 で A5/WeaklyInitialAndDescent から移動）。
規約：D_comp(A) の余極限。
使われ方：有限生成への帰着、A5-2 (δ)。 -/
theorem prismaticPerfection_filteredColimit (hR : IsIntegralPerfectoid R p)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity I]
    (D : (SSet.uliftFunctor.{u+1,u}).obj I ⟶ algebraNerve R) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (completePerfectionFunctor (E := E) p R hR) c) := by
  sorry -- 離散環の filtered 余極限を取ってからの animated p 完備化は D32 で Δ を変えない。
        -- sifted 保存と colim_φ の交換、(p,d) 完備化の反射により指定余錐は完備圏で余極限


-- Example 8.3（`perfectoidization_charP`、Prop 8.5 の後）は drafts/A4/AfterComparison.lean へ（W9-III-09）。

end SerrePositivity.BhattScholze.Perfectoidization.Derived
