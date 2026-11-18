module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeUnderMap

/-!
概要：元の大域 coslice 写像の射影は、同じ元の通常 frame 図式の閉 nerve である。
方針：join の右包含を最初の面へ戻し、同じ cone 単体の通常末尾面を回収する。
規約：元の全通常図式を厳密に保持する。使われ方：同じ実 cone と屋根評価の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementNerveDiagram :
    nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) :=
  nerveMap (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) ≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion A (Complex A)

lemma normalizedTensorElementNerveDiagram_app {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y).app (Opposite.op ⦋n⦌) c =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A) := rfl

lemma normalizedTensorConeUnderMap_projection :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderMap A X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X) =
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro c
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) Δ[n] ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c))) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex (c ⋙ _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A X Y ⋙ _root_.SerrePositivity.ComplexLimits.complexToClosed A)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso_inr,
    SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  change (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c).pullback
    (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom = _
  have hδ : (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom =
      (Fin.succOrderEmb (n + 1)).toOrderHom := by
    apply DFunLike.ext
    intro i
    change (0 : Fin (n + 2)).succAbove i = i.succ
    rw [Fin.succAbove_zero]
  rw [hδ]
  exact _root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex_tail A X Y c

end SerrePositivity.ComplexLimits
