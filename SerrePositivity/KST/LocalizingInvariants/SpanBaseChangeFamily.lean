module
public import SerrePositivity.KST.LocalizingInvariants.IntervalPrecompositionFamily

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.SquareArrowFamily
public import SerrePositivity.KST.LocalizingInvariants.SpanPostcompositionFamily

/-!
概要：指定した正方形の右辺を持つ span を、第一終点を固定した実 span の辺へ拡張する。
方針：正方形の底辺で第一脚を前合成し、その族を元の正方形の右脚の族と貼る。
規約：元の正方形全体・最終 span・第一終点を厳密に保持する。
使われ方：Ore pullback から cartesian lift 候補を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma exists_spanBaseChangeFamily {X : SSet.{u}} [Quasicategory X]
    (p : (horn 2 0 : SSet.{u}) ⟶ X) (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ R = horn₂₀.ι₀₂ ≫ p) :
    ∃ (T : (Δ[2] : SSet.{u}) ⟶ X)
      (F : (Δ[1] : SSet.{u}) ⟶ (ihom (horn 2 0 : SSet.{u})).obj X),
      stdSimplex.δ (2 : Fin 3) ≫ T = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R ∧
      stdSimplex.δ (0 : Fin 3) ≫ T = horn₂₀.ι₀₁ ≫ p ∧
      stdSimplex.δ (0 : Fin 2) ≫ F = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) ∧
      F ≫ (pre horn₂₀.ι₀₁).app X = intervalPrecompositionFamily T ∧
      F ≫ (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R ∧
      F ≫ (pre horn₂₀.ι₀₁).app X ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          SSet.const ((horn₂₀.ι₀₁ ≫ p).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ∧
      F ≫ (pre horn₂₀.ι₀₂).app X ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R := by
  have hc : stdSimplex.δ (0 : Fin 2) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R) =
      stdSimplex.δ (1 : Fin 2) ≫ (horn₂₀.ι₀₁ ≫ p) := by
    have hcorner : stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge.{u} =
        stdSimplex.δ (1 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge := by
      apply SSet.yonedaEquiv.injective
      apply Prod.ext <;> decide
    have hsource : stdSimplex.δ (1 : Fin 2) ≫
        (horn₂₀.ι₀₂ : (Δ[1] : SSet.{u}) ⟶ horn 2 0) =
        stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁ := by
      apply SSet.yonedaEquiv.injective
      decide
    rw [← Category.assoc, hcorner, Category.assoc, hR, ← Category.assoc,
      hsource, Category.assoc]
  obtain ⟨T, hT₂, hT₀, hL₁, hLs, hLt⟩ :=
    exists_intervalPrecompositionFamily (horn₂₀.ι₀₁ ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R) hc
  have hLR : intervalPrecompositionFamily T ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    rw [hLs, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily_source]
  let F := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows (intervalPrecompositionFamily T) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R) hLR
  have hFl : F ≫ (pre horn₂₀.ι₀₁).app X = intervalPrecompositionFamily T :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_left _ _ _
  have hFr : F ≫ (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamilyOfArrows_right _ _ _
  refine ⟨T, F, hT₂, hT₀, ?_, hFl, hFr, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stable_spanFamily_hom_ext
    · rw [Category.assoc, hFl, hL₁, SSet.const_comp]
      rfl
    · rw [Category.assoc, hFr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily_one, hR, SSet.const_comp]
      rfl
  · rw [← Category.assoc, hFl]
    exact hLt
  · rw [← Category.assoc, hFr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily_target]

end SerrePositivity.KST.LocalizingInvariants
