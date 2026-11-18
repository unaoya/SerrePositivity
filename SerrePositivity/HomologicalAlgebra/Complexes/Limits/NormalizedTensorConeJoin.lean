module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorConeProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness

/-!
概要：元の全反対要素圏上の実 cone を、点とその nerve の join からの大域射として構成する。
方針：同じ coslice 写像を uncurry し、先端・通常図式・全単体への制限を厳密に回収する。
規約：同じ元の先端 X と全通常 frame 図式を保つ。使われ方：元の屋根との大域比較。
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

def normalizedTensorConeJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderMap A X Y)

lemma normalizedTensorConeJoin_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin A X Y = _root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderMap A X Y)

lemma normalizedTensorConeJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin A X Y = _root_.SerrePositivity.ComplexLimits.normalizedTensorElementNerveDiagram A X Y := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderMap_projection]

lemma normalizedTensorConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin A X Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
          (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeSimplex A X Y c) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    SSet.yonedaEquiv_symm_comp, _root_.SerrePositivity.ComplexLimits.normalizedTensorConeUnderMap_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  rfl

end SerrePositivity.ComplexLimits
