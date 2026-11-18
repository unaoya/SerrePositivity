module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorDoubleConeOverProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：元の先端 X・全 frame 図式・終端 X を持つ実大域二重 join を構成する。
方針：同じ slice 内の大域 cone を uncurry し、前面・終端・両先端の恒等族を回収する。
規約：全元単体への制限も同じ実二重 cone を保つ。使われ方：元の augmentation 三角形。
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

def normalizedTensorDoubleConeJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))) Δ[0] ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin A X Y)

lemma normalizedTensorDoubleConeJoin_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))) Δ[0] ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeJoin A X Y = _root_.SerrePositivity.ComplexLimits.normalizedTensorConeJoin A X Y := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeJoin, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin_projection]

lemma normalizedTensorDoubleConeJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y))) Δ[0] ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeJoin A X Y = _root_.SerrePositivity.ComplexLimits.normalizedTensorConePoint A X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin A X Y)

lemma normalizedTensorDoubleConeJoin_endpoints :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)))
      (𝟙 Δ[0]) ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeJoin A X Y =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).symm X) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeJoin, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin_inl, _root_.SerrePositivity.ComplexLimits.normalizedTensorIdentityOverPoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
  rfl

lemma normalizedTensorDoubleConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c)) (𝟙 Δ[0]) ≫
      _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeJoin A X Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom (𝟙 Δ[0]) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso (n + 1) 0).hom ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))).symm
            (_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeSimplex A X Y c) := by
  rw [_root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeJoin, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp,
    _root_.SerrePositivity.ComplexLimits.normalizedTensorDoubleConeOverJoin_restrict_simplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceOverUncurry_yoneda]
  rfl

end SerrePositivity.ComplexLimits
