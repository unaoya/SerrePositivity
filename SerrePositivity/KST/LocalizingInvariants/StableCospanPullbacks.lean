module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableSpanPushout
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableOpposite

/-!
概要：安定な quasicategory の任意の指定二辺の cospan に、実普遍 pullback を構成する。
方針：SConstruction の任意 span の押し出しを読み取り専用で使い、二重反対から戻す。
規約：入力の二辺を厳密に保持。使われ方：普遍な Ore 四角形と分母の基底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma dualSquare_topEdge {X : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.dualSquare R = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R) := by
  apply SSet.yonedaEquiv.injective
  rfl

lemma reverse_edgeOp_unop {X : SSet.{u}} {x y : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex 1 ((SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f).edge) ≫
        (SSet.opFunctorCompOpFunctorIso.app X).hom = SSet.yonedaEquiv.symm f.edge := by
  apply SSet.yonedaEquiv.injective
  change (SSet.yonedaEquiv.symm f.edge).app (Opposite.op ⦋1⦌) _ =
    (SSet.yonedaEquiv.symm f.edge).app (Opposite.op ⦋1⦌) _
  congr 1
  apply stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma exists_stable_pullbackSquare_of_edges {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y z : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : Truncated.Edge (X := (truncation 2).obj X) y z) :
    ∃ R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ R = SSet.yonedaEquiv.symm f.edge ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R = SSet.yonedaEquiv.symm g.edge := by
  obtain ⟨S, hS, hP⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_stable_pushoutSquare_of_span
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan (X := X.op) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp g))
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ S =
      (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp f).edge := by
    have h := congrArg (horn₂₀.ι₀₁ ≫ ·) hS
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left (X := X.op)] at h
    exact h
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ S =
      (SSet.yonedaEquiv (X := X.op) (n := ⦋1⦌)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp g).edge := by
    have h := congrArg (horn₂₀.ι₀₂ ≫ ·) hS
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge,
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right (X := X.op)] at h
    exact h
  let q := (SSet.opFunctorCompOpFunctorIso.app X).hom
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.dualSquare S ≫ q, ?_, ?_, ?_⟩
  · exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_postcomp_isIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.dualSquare S) q).mp
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPushoutSquare_iff_dualSquare S).mp hP)
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.dualSquare_rightEdge, hb]
    exact reverse_edgeOp_unop f
  · rw [← Category.assoc, dualSquare_topEdge, hl]
    exact reverse_edgeOp_unop g

lemma stable_hasLimit_edgeCospan {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y z : X _⦋0⦌}
    (f : Truncated.Edge (X := (truncation 2).obj X) x z)
    (g : Truncated.Edge (X := (truncation 2).obj X) y z) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan f g) := by
  obtain ⟨R, hR, hr, ht⟩ := exists_stable_pullbackSquare_of_edges f g
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan R = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan f g := by
    apply horn₂₂.isPushout.hom_ext
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge, hr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_left]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge, ht, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_right]
  rw [← hc]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone R, hR⟩

lemma exists_edgeCospan_presentation {X : SSet.{u}} (p : (horn 2 2 : SSet.{u}) ⟶ X) :
    ∃ (x y z : X _⦋0⦌)
      (f : Truncated.Edge (X := (truncation 2).obj X) x z)
      (g : Truncated.Edge (X := (truncation 2).obj X) y z), _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan f g = p := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p))
  let t := SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ p)
  have ht : X.δ 0 t = X.δ 0 f.edge := by
    change X.δ 0 (SSet.yonedaEquiv (horn₂₂.ι₁₂ ≫ p)) =
      X.δ 0 (SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ p))
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← stdSimplex.yonedaEquiv_δ_comp]
    apply congrArg SSet.yonedaEquiv
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ p) horn₂₂.isPushout.w.symm).trans (Category.assoc _ _ _))
  let g : Truncated.Edge (X := (truncation 2).obj X) (X.δ 1 t) (X.δ 0 f.edge) :=
    ⟨t, rfl, ht⟩
  refine ⟨_, _, _, f, g, ?_⟩
  apply horn₂₂.isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_left]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan_right]
    exact SSet.yonedaEquiv.symm_apply_apply _

lemma stable_hasLimit_cospan {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (p : (horn 2 2 : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p := by
  obtain ⟨_, _, _, f, g, rfl⟩ := exists_edgeCospan_presentation p
  exact stable_hasLimit_edgeCospan f g

end SerrePositivity.KST.LocalizingInvariants
