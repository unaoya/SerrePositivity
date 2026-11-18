module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeJoin

/-!
概要：slice 内の大域二重 cone の通常図式と、元の frame 図式への射影を回収する。
方針：元の恒等錐の点評価と、二つの大域射影の厳密な一致を使う。
規約：同じ全図式を保つ。使われ方：slice prism の両端と全底円柱。
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

lemma normalizedTensorIdentityOverPoint_vertex :
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorIdentityOverPoint A X).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X) := by
  have hp : SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})) := by
    apply SSet.stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [hp]
  exact SSet.yonedaEquiv_symm_app_id _

def normalizedTensorDoubleConeOverDiagram : nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X) :=
  _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeUnderOverMap A X Y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.ComplexLimits.normalizedTensorIdentityOverPoint A X)

lemma normalizedTensorDoubleConeOverJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin A X Y = _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram A X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeUnderOverMap A X Y)

lemma normalizedTensorDoubleConeOverDiagram_projection :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverDiagram A X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X) =
        _root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y := by
  rw [← _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin_inr, Category.assoc,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin_projection, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin_inr]

end SerrePositivity.ComplexLimits
