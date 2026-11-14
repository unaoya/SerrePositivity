-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Derived.Animated（仮。原典 Def 8.2 の定義域どおりの版、Construction 7.6 (5) の相対版、Prop 8.13）
-- 設計書：formalization-plans/bhatt-scholze/a7-design.md §2.1・§2.2、単位 A7-1。基準コミット efa846fe8。型検査対象（5∞-0）。
module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Hom
public import Mathlib.CategoryTheory.Elements
-- 本ファイルは drafts/A2/{AnimatedAlgebra,DerivedPrismaticCohomology,BaseChangeAndTensor}.lean、drafts/A4/{Perfectoidization,InterfaceFields}.lean、
-- drafts/DerivedGeneral/CompletionFunctor.lean、drafts/A7/AnimatedDomain.lean（G-A7-1。W9-II-24 で切り出し）を import する。

/-!
# animated 代数上の perfectoid 化と対称モノイダル性（BS 著者版 Def 8.2 の定義域、Prop 8.13）

## 概要
原典 Def 8.2 の定義域「導来 p 完備な単体的 R 代数」を `AnimatedAlgebra R`（A2-1 の P_Σ(Poly_R)）の充満部分 ∞ 圏 `CompleteAnimatedAlgebra R` として
取り、その上で Δ_{S/A,perf} と S_perfd を定義する（D60）。A4 の離散版はその `discreteToAnimated` に沿う制限。Construction 7.6 (5) の相対版
Δ_{S_1 ⊗̂_{S_3} S_2} ≃ Δ_{S_1} ⊗̂_{Δ_{S_3}} Δ_{S_2} を経て Prop 8.13：S_{1,perfd} ⊗̂^L_{S_{3,perfd}} S_{2,perfd} ≃ (S_1 ⊗̂^L_{S_3} S_2)_perfd。

## 方針
相対テンソル（押し出し）は bar 構成の sifted 余極限（G-A7-2）、Δ は sifted 余極限と絶対テンソル（A2-4 の (5)）を保つ。完全化 colim_φ・
(p,d) 完備化・⊗ A/d はいずれも相対テンソルと可換（G-A7-4）。

## 規約
基底は Not 8.1 の完全 prism（R = A/d）。値は CAlg_A・CAlg_R。導来 p 完備性は底の D(R) 対象（`animatedForget`）で。

## 使われ方
Cor 8.14（A7-2：X = S_perfd ⊗̂^L_S S_perfd の perfd）、Thm 10.11（A8）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.Prismatic SerrePositivity.InfinityCategories SerrePositivity.EInfinity

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p)

/-! ## G-A7-2：相対テンソル -/

abbrev TensorSpan (E : SSet.{u+1}) := (horn 2 0 : SSet.{u+1}) ⟶ E

/-- 左脚 0→1 と右脚 0→2 を保つ押し出し余錐。 -/
abbrev TensorCocone {E : SSet.{u+1}} (D : TensorSpan E) :=
  { c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D // _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c }

def animatedPushout (D : TensorSpan (AnimatedAlgebra R)) : TensorCocone D := by
  sorry -- P_Σ(Poly_R) の余極限。二つの構造射はこの余錐の脚

/-- 概要：AnimatedAlgebra の押し出し S_1 ⊔_{S_3} S_2（相対テンソル S_1 ⊗^L_{S_3} S_2）は bar 構成 S_1 ⊗ S_3^{⊗•} ⊗ S_2 の幾何学的実現（sifted 余極限）。
方針：P_Σ の押し出しは Poly 上の押し出し（多項式環のテンソル）の sifted 余極限で生成（HA 4.4.2.8 の類似）。
規約：完備版は `animatedCompletion` を当てる。
使われ方：(5) の相対版。 -/
def relativeTensor (D : TensorSpan (AnimatedAlgebra R)) : (AnimatedAlgebra R) _⦋0⦌ :=
  (animatedPushout R D).1.vertex

/-- [n]→[1] が定数 0、非定数、定数 1 のとき、それぞれ左端、中央、右端へ。
制限で非定数が定数に移る二つの場合が D の二つの構造射を与える。 -/
def barLabels : (SSet.uliftFunctor.{u+1,0}).obj (nerve (Δ[1] : SSet.{0}).Elements) ⟶
    (horn 2 0 : SSet.{u+1}) := by
  classical
  let label (e : (Δ[1] : SSet.{0}).Elements) : Fin 3 :=
    if stdSimplex.objEquiv e.val = SimplexCategory.const _ _ 0 then 1 else
    if stdSimplex.objEquiv e.val = SimplexCategory.const _ _ 1 then 2 else 0
  exact Classical.choose (show ∃ L : (SSet.uliftFunctor.{u+1,0}).obj (nerve (Δ[1] : SSet.{0}).Elements) ⟶
      (horn 2 0 : SSet.{u+1}), ∀ e,
      (L.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex e))).val = stdSimplex.obj₀Equiv.symm (label e) from by
    sorry) -- label の鎖は常に 0→1 または 0→2 の辺に含まれ、頂点で単体を決める

abbrev barProjection := (SSet.uliftFunctor.{u+1,0}).map
  (nerveMap (Functor.Elements.π (Δ[1] : SSet.{0})))

/-- 射影の離散ファイバーで余積を取る左 Kan 延長。次数 n は
S₁ ⊗ S₃^⊗n ⊗ S₂、面は両端の作用または fold、退化は単位の挿入。 -/
def twoSidedBar (D : TensorSpan (AnimatedAlgebra R)) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve (SimplexCategoryᵒᵖ)) ⟶ AnimatedAlgebra R :=
  Classical.choose (show ∃ B, ∃ η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (barLabels ≫ D) (barProjection ≫ B),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtensionHom barProjection (barLabels ≫ D) B η from by
    sorry) -- 有限余積で点ごとに構成する。射は同じ添字の写像に沿う

theorem relativeTensor_eq_bar (D : TensorSpan (AnimatedAlgebra R)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (twoSidedBar R D), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ c.vertex = relativeTensor R D := by
  sorry -- 相対テンソルの二脚から標準増大を作る。bar の幾何学的実現はこの押し出し

/-- 押し出し余錐をそのまま送って余極限となる条件。 -/
def PreservesTensorSpans {E V : SSet.{u+1}} (F : E ⟶ V) : Prop :=
  ∀ (D : TensorSpan E) (c : TensorCocone D), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c.1)

/-- 概要：sifted 余極限と絶対テンソル（余積）を保つ関手は相対テンソルを保つ。
方針：bar 構成の各項が絶対テンソルで、実現が sifted 余極限。
規約：—
使われ方：Δ、colim_φ、完備化、⊗ A/d。 -/
theorem preservesRelativeTensor_of_siftedAndTensor {E V : SSet.{u+1}} [Quasicategory E] [Quasicategory V]
    (F : E ⟶ V) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits F)
    (hex : ∀ x y : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y))
    (ht : ∀ (x y : E _⦋0⦌) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)) : PreservesTensorSpans F := by
  sorry -- 有限非空余積で二側 bar の各項を送り、Δᵒᵖ の sifted 実現を hs で送る

/-- R ≃ A/d による animated 基底の同定は polyYoneda からの sifted 延長。 -/
def animatedDelta (hR : IsIntegralPerfectoid R p) :
    CompleteAnimatedAlgebra p R ⟶ CompleteCAlg (E := E) (perfectPrism p R hR) := by
  let P := perfectPrism p R hR
  let change : AnimatedAlgebra R ⟶ AnimatedAlgebra (perfectPrismRing p R ⧸ P.ideal) := by
    sorry -- 要確認：A2 の基底同型に沿う移送。perfectPrism_quotientEquiv の制限
  exact animatedCompleteInclusion p R ≫ change ≫ derivedPrismaticCohomology (E := E) P (hP := perfectPrism_bounded p R hR)

/-- 概要：Construction 7.6 (5) の相対版：Δ_{S_1 ⊗̂_{S_3} S_2} ≃ Δ_{S_1} ⊗̂_{Δ_{S_3}} Δ_{S_2}（CAlg_A の相対テンソルの完備化）。
方針：A2-4 `derivedPrismaticCohomology_tensor`・`derivedPrismaticCohomology_siftedColimit`、`preservesRelativeTensor_of_siftedAndTensor`、D32 で完備化を通す。
規約：—
使われ方：Prop 8.13。 -/
theorem derivedPrismaticCohomology_relativeTensor (hR : IsIntegralPerfectoid R p) :
    PreservesTensorSpans (animatedDelta (E := E) p R hR) := by
  sorry -- A2-4 の絶対テンソルと sifted 余極限の保存。D32 で入力の p 完備化を通す

/-! ## Def 8.2（animated 版） -/

/-- A2 の Frobenius を関手圏の辺として受ける。 -/
def animatedDeltaFrobenius (hR : IsIntegralPerfectoid R p) :
    let H := animatedDelta (E := E) p R hR ≫ completeCAlgInclusion (E := E) (p := p) (perfectPrism p R hR)
    ((ihom (CompleteAnimatedAlgebra p R)).obj (E.CAlg (perfectPrismRing p R))).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift)) := by
  sorry -- 要確認：A2 の derivedPrismaticFrobenius の animated 自然変換。離散成分は A4 の discreteDeltaFrobenius

/-- 関手圏で τ を正に反復する。頂点は関手、後続辺は τⁿ(φ)。 -/
def frobeniusFunctorTower {E V : SSet.{u+1}} [Quasicategory V]
    (τ : V ⟶ V) (H : E ⟶ V)
    (φ : ((ihom E).obj V).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ τ))) :
    frobeniusTowerShape.{u} ⟶ (ihom E).obj V :=
  restrictionSequence ((ihom E).map τ) (x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) φ

def frobeniusFunctorColimit {E V : SSet.{u+1}} [Quasicategory V]
    (τ : V ⟶ V) (H : E ⟶ V)
    (φ : ((ihom E).obj V).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ τ)))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (frobeniusFunctorTower τ H φ)) : E ⟶ V :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv E V).symm hc.choose.vertex

abbrev animatedDeltaUnderlying (hR : IsIntegralPerfectoid R p) :=
  animatedDelta (E := E) p R hR ≫ completeCAlgInclusion (E := E) (p := p) (perfectPrism p R hR)

abbrev animatedTower (hR : IsIntegralPerfectoid R p) :=
  frobeniusFunctorTower (cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift)
    (animatedDeltaUnderlying (E := E) p R hR) (animatedDeltaFrobenius (E := E) p R hR)

theorem animatedTower_hasColimit (hR : IsIntegralPerfectoid R p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (animatedTower (E := E) p R hR) := by
  sorry -- G-A4-2：関手圏の点ごとの sequential 余極限

def animatedFrobeniusColimit (hR : IsIntegralPerfectoid R p) :
    CompleteAnimatedAlgebra p R ⟶ E.CAlg (perfectPrismRing p R) :=
  frobeniusFunctorColimit (cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift)
    (animatedDeltaUnderlying (E := E) p R hR) (animatedDeltaFrobenius (E := E) p R hR) (animatedTower_hasColimit (E := E) p R hR)

/-- 関手圏で選んだ余極限の第0脚。始点と終点だけを頂点表示に移す。 -/
def animatedTowerLeg (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (animatedDeltaUnderlying (E := E) p R hR) (animatedFrobeniusColimit (E := E) p R hR) := by
  let c := (animatedTower_hasColimit (E := E) p R hR).choose
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg c (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (0 : ℕ)))
  exact eqToHom (by sorry) ≫ SSet.Truncated.HomotopyCategory.homMk l.toTruncated ≫
    eqToHom (by sorry) -- 塔の第0頂点と functorVertexEquiv の往復

/-- 概要：Δ_{S/A,perf} : CompleteAnimatedAlgebra R ⟶ CAlg_A：A2-2 の Δ の制限の Frobenius の塔の余極限の (p,d) 完備化（A4-1 の構成を関手の段で）。
方針：A4-3 の `prismaticPerfectionFunctor` と同じ構成、定義域だけ animated。
規約：—
使われ方：`perfectoidizationAnimated`。 -/
def prismaticPerfectionAnimated (hR : IsIntegralPerfectoid R p) :
    CompleteAnimatedAlgebra p R ⟶ E.CAlg (perfectPrismRing p R) :=
  animatedFrobeniusColimit (E := E) p R hR ≫ prismCAlgCompletion (E := E) (p := p) (perfectPrism p R hR)

/-- 概要：S_perfd := Δ_perf ⊗^L_A A/d : CompleteAnimatedAlgebra R ⟶ CAlg_R。原典 Def 8.2 (2) の定義域どおりの版。
方針：底変換 CAlg_A → CAlg_R（G-A4-4）。
規約：p 完備な E∞-S 代数。
使われ方：Prop 8.13、Cor 8.14。 -/
def perfectoidizationAnimated (hR : IsIntegralPerfectoid R p) :
    CompleteAnimatedAlgebra p R ⟶ E.CAlg R :=
  prismaticPerfectionAnimated (E := E) p R hR ≫ modPrismFunctor (E := E) p R hR

/-- 概要：離散版との一致：`discreteToAnimated ≫ perfectoidizationAnimated` は A4-3 の `perfectoidizationFunctor`（点ごとに A4-1 の `perfectoidization`）。
方針：定義の展開（Δ の離散版は `derivedPrismaticCohomologyDiscrete`）。
規約：E3 の欄 `e3Perfd` はこれにより変わらない。
使われ方：E3、A5。 -/
def perfectoidizationAnimated_discrete (hR : IsIntegralPerfectoid R p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (completeDiscreteToAnimated p R ≫ perfectoidizationAnimated (E := E) p R hR)
      (nerveMap (PerfectoidizationInterface.completeInclusion R p) ≫ perfectoidizationFunctor (E := E) p R hR) := by
  sorry -- discreteDeltaFrobenius は同じ塔の離散成分。余極限、reflectCompleteCAlg、modPrismFunctor の自然性

/-! ## Prop 8.13 -/

/-- 概要：G-A7-4：colim_φ は φ 両立の相対テンソルと可換（sequential 余極限の対角）；完備化は対称モノイダルな局所化；⊗ A/d は cofib(d)。
方針：G-A4-2・G-A2-3・G-A5-3 の隣。
規約：—
使われ方：Prop 8.13。 -/
theorem frobeniusColimit_relativeTensor {E V : SSet.{u+1}} [Quasicategory V]
    (τ : V ⟶ V) (hτ : PreservesTensorSpans τ) (H : E ⟶ V)
    (φ : ((ihom E).obj V).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ τ)))
    (hseq : ∀ D : frobeniusTowerShape.{u} ⟶ V, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D)
    (hcol : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (frobeniusFunctorTower τ H φ)) (hH : PreservesTensorSpans H) :
    PreservesTensorSpans (frobeniusFunctorColimit τ H φ hcol) := by
  sorry -- 各段の押し出しを τ が保ち、点ごとの余極限を交換。有限個の塔には ℕ→ℕ^r の共終な対角を使う。
        -- 完全 prism では τ=Res_{φ_A} は自己同値で、完備圏にも restrictFrobeniusCompletion で移る

theorem restrictFrobenius_preservesTensorSpans (hR : IsIntegralPerfectoid R p) :
    PreservesTensorSpans (cAlgRestrictScalars (E := E) (perfectPrism p R hR).deltaStructure.frobeniusLift) := by
  sorry -- φ_A は自己同型。cAlgRestrictScalars_comp・id で逆に沿う制限と互いに逆

/-- 完備圏で上の τ を読む。完備対象に τ を適用した後の反射単位は同値。 -/
def completeFrobeniusRestriction (hR : IsIntegralPerfectoid R p) :
    CompleteCAlg (E := E) (perfectPrism p R hR) ⟶ CompleteCAlg (E := E) (perfectPrism p R hR) :=
  let P := perfectPrism p R hR
  completeCAlgInclusion (E := E) (p := p) P ≫ cAlgRestrictScalars (E := E) P.deltaStructure.frobeniusLift ≫ reflectCompleteCAlg (E := E) (p := p) P

theorem completeFrobeniusRestriction_preservesTensorSpans (hR : IsIntegralPerfectoid R p) :
    PreservesTensorSpans (completeFrobeniusRestriction (E := E) p R hR) := by
  sorry -- restrictFrobeniusCompletion で完備圏に自己同値を制限する。
        -- frobeniusColimit_relativeTensor を H = animatedDelta に適用するための hτ

theorem completion_relativeTensor {A : Type u} [CommRing A] (P : OrientedPrism p A) :
    PreservesTensorSpans (reflectCompleteCAlg (E := E) (p := p) P) := by
  sorry -- 反射は左随伴。押し出しの標的は (p,d) 完備な圏

abbrev CompletePCAlg : SSet.{u+1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (E.CAlg R) (fun x => isPCompleteVertex p R ((E.forget R).app _ x))

def completeModD (hR : IsIntegralPerfectoid R p) :
    CompleteCAlg (E := E) (perfectPrism p R hR) ⟶ CompletePCAlg (E := E) p R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (completeCAlgInclusion (E := E) (p := p) (perfectPrism p R hR) ≫ modPrismFunctor (E := E) p R hR)
    (by sorry) -- 完備な代数の mod d の底は cofib(d) で p 完備

theorem modD_relativeTensor (hR : IsIntegralPerfectoid R p) :
    PreservesTensorSpans (completeModD (E := E) p R hR) := by
  sorry -- 底変換の左随伴性と完備化。mod d 後の完備化は p 完備化

def perfdComplete (hR : IsIntegralPerfectoid R p) :
    CompleteAnimatedAlgebra p R ⟶ CompletePCAlg (E := E) p R :=
  animatedFrobeniusColimit (E := E) p R hR ≫ reflectCompleteCAlg (E := E) (p := p) (perfectPrism p R hR) ≫ completeModD (E := E) p R hR

theorem perfdComplete_forget (hR : IsIntegralPerfectoid R p) :
    perfdComplete (E := E) p R hR ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (E.CAlg R)
      (fun x => isPCompleteVertex p R ((E.forget R).app _ x))).ι =
        perfectoidizationAnimated (E := E) p R hR := by
  rfl -- fullSubcomplexLift の証明成分を忘れる

/-- 完備 animated 代数の span の押し出し。 -/
def completeAnimatedPushout (D : TensorSpan (CompleteAnimatedAlgebra p R)) : TensorCocone D := by
  sorry -- animatedPushout の余錐を animatedCompletion で送り、完備な入力で単位を逆にする

def perfdTensorPushout (hR : IsIntegralPerfectoid R p) (D : TensorSpan (CompleteAnimatedAlgebra p R)) :
    TensorCocone (D ≫ perfdComplete (E := E) p R hR) := by
  sorry -- CAlg_R の押し出しを p 完備化して得る余錐

/-- 概要：Prop 8.13 の比較射 S_{1,perfd} ⊗̂^L_{S_{3,perfd}} S_{2,perfd} → (S_1 ⊗̂^L_{S_3} S_2)_perfd（CAlg_R の押し出しの完備化の普遍性と perfd の関手性）。 -/
def perfectoidization_relativeTensorMap (hR : IsIntegralPerfectoid R p) (D : TensorSpan (CompleteAnimatedAlgebra p R)) :
    let F := perfdComplete (E := E) p R hR
    (CompletePCAlg (E := E) p R).Edge (perfdTensorPushout (E := E) p R hR D).1.vertex
      (F.app _ (completeAnimatedPushout p R D).1.vertex) := by
  let c := (perfdTensorPushout (E := E) p R hR D).1
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (perfdComplete (E := E) p R hR) (completeAnimatedPushout p R D).1
  let comparison : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (D ≫ perfdComplete (E := E) p R hR)).Edge c d := by
    sorry -- c は余錐の圏で始対象。両脚・中央の整合を保つ辺
  exact comparison.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection _)

/-- 概要：Prop 8.13：比較射は同値（任意の導来 p 完備な animated S_1 ← S_3 → S_2）。
方針：`derivedPrismaticCohomology_relativeTensor` に `frobeniusColimit_relativeTensor`・`completion_relativeTensor`・`modD_relativeTensor` を当てる。
規約：原典の形。E3 で使うのは S_1 = S_2 = S_perfd、S_3 = S（離散）。
使われ方：Cor 8.14、Thm 10.11、BR31。 -/
theorem perfectoidization_relativeTensor (hR : IsIntegralPerfectoid R p) (D : TensorSpan (CompleteAnimatedAlgebra p R)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectoidization_relativeTensorMap (E := E) p R hR D).toTruncated := by
  sorry -- Δ の完備押し出しに完備圏で frobeniusColimit_relativeTensor を適用。
        -- 反射が余極限を保つので raw な塔を最後に完備化した値に一致し、modD_relativeTensor で結ぶ

end SerrePositivity.BhattScholze.Perfectoidization.Derived
