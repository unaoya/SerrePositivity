module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionConeComparison

/-!
概要：元の評価錐と companion 極限錐の比較の、実際の左右の三単体と全ての面。
方針：元の strict cospan の二射の nerve 単体で比較の join 図式を制限する。
規約：同じ比較辺と apex の BF 射を保持。使われ方：元の Hom 正方形による符号判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleConeComparisonCellsSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の strict cospan の同じ二つの底の区間を、大きい宇宙の nerve 内で表示する。 -/
def circleConeComparisonParameter (k : WalkingPair) :
    (Δ[1] : SSet.{u + 1}) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)) :=
  SSet.yonedaEquiv.symm (ULift.up (LoopEdgewiseSection.arrow k))

/-- 同じ二つの底の区間の終点は、元の中央の対象の同じ頂点。 -/
lemma circleConeComparisonParameter_target_common :
    stdSimplex.δ (0 : Fin 2) ≫ circleConeComparisonParameter.{u} .left =
      stdSimplex.δ (0 : Fin 2) ≫ circleConeComparisonParameter .right := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp]
  simp only [circleConeComparisonParameter, Equiv.apply_symm_apply]
  apply ULift.ext
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · fin_cases i
    rfl
  · intros
    exact Subsingleton.elim _ _

/-- 元の評価錐の同じ底の区間上の、実際の三角形。 -/
def circleNativeComparisonTriangle (z : Sp.{u} _⦋0⦌) (k : WalkingPair) : Sp.{u} _⦋2⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleMap
    (nativeCircleStrictCone z) (circleConeComparisonParameter k))

/-- 元の比較辺の左右の底の区間上の、実際の三単体。 -/
def circleCompanionComparisonTetrahedron (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    Sp.{u} _⦋3⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexMap
    (circleCompanionConeComparison z) (circleConeComparisonParameter k))

/-- 元の比較辺の中央の対象上の、両三単体に共通する三角形。 -/
def circleCompanionComparisonCentralTriangle (z : Sp.{u} _⦋0⦌) : Sp.{u} _⦋2⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexFaceMap (circleCompanionConeComparison z)
    (stdSimplex.δ (0 : Fin 2) ≫ circleConeComparisonParameter .left))

/-- 元の比較辺の二つの一点の対象上の、同じ比較三角形。 -/
def circleCompanionComparisonBranchTriangle (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    Sp.{u} _⦋2⦌ :=
  SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexFaceMap (circleCompanionConeComparison z)
    (stdSimplex.δ (1 : Fin 2) ≫ circleConeComparisonParameter k))

/-- 零面は、元の companion 錐の前工程の同じ反転三角形そのもの。 -/
lemma circleCompanionComparisonTetrahedron_zero (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    Sp.δ 0 (circleCompanionComparisonTetrahedron z k) = circleCompanionReflectedTriangle z k := by
  rw [circleCompanionComparisonTetrahedron, ← stdSimplex.yonedaEquiv_δ_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexMap_zero]
  change circleCompanionBKCoherentConeSimplex z (LoopEdgewiseSection.arrow k) = _
  exact circleCompanionBKCoherentConeSimplex_triangle z k

/-- 一面は、元の評価錐の同じ底の区間上の三角形そのもの。 -/
lemma circleCompanionComparisonTetrahedron_one (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    Sp.δ 1 (circleCompanionComparisonTetrahedron z k) = circleNativeComparisonTriangle z k := by
  rw [circleCompanionComparisonTetrahedron, ← stdSimplex.yonedaEquiv_δ_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexMap_one]
  rfl

/-- 二面は、二つの底の区間に共通する中央の三角形そのもの。 -/
lemma circleCompanionComparisonTetrahedron_two (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    Sp.δ 2 (circleCompanionComparisonTetrahedron z k) =
      circleCompanionComparisonCentralTriangle z := by
  rw [circleCompanionComparisonTetrahedron, ← stdSimplex.yonedaEquiv_δ_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexMap_two]
  cases k
  · rfl
  · rw [← circleConeComparisonParameter_target_common]
    rfl

/-- 三面は、元の一点の対象上の同じ比較三角形そのもの。 -/
lemma circleCompanionComparisonTetrahedron_three (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    Sp.δ 3 (circleCompanionComparisonTetrahedron z k) =
      circleCompanionComparisonBranchTriangle z k := by
  rw [circleCompanionComparisonTetrahedron, ← stdSimplex.yonedaEquiv_δ_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexMap_three]
  rfl

/-- 同じ三単体の最初の辺は、元の比較の BF 自己射そのもの。 -/
lemma circleCompanionComparisonTetrahedron_apex (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 0 1 (by decide)) ≫
      SSet.yonedaEquiv.symm (circleCompanionComparisonTetrahedron z k) =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleCompanionConeComparisonHom z)).edge := by
  rw [circleCompanionComparisonTetrahedron, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexMap_apex_edge]
  exact circleCompanionConeComparisonExtension_apex z

/-- 同じ三単体の最後の辺は、元の底の strict 図式の同じ区間。 -/
lemma circleCompanionComparisonTetrahedron_base (z : Sp.{u} _⦋0⦌) (k : WalkingPair) :
    SSet.yonedaEquiv.symm (stdSimplex.edge 3 2 3 (by decide)) ≫
      SSet.yonedaEquiv.symm (circleCompanionComparisonTetrahedron z k) =
    circleConeComparisonParameter k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      (pointLoopDiagram (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  rw [circleCompanionComparisonTetrahedron, Equiv.symm_apply_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexMap_base_edge]

end SerrePositivity.KST.Spectra.OmegaSpectrum
