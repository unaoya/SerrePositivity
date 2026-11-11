module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorTriangleMap
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeFamily
public import SerrePositivity.EInfinity.FrameHom.MixedNerveConstant
/-! 概要：元の大域評価三角形は全関手圏内で同じ全族の合成を与える。
方針：元の全三辺を持つ二単体族を curry する。
規約：全 K と元の円柱を保持。使われ方：同じ導来 roof との大域比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
def normalizedTensorEvaluationHomotopy :
    SSet.Homotopy (normalizedTensorElementNerveDiagram A X Y)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) := by
  let T := nerveMap (complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion A (Complex A)
  refine _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget
    (HomotopyClasses.postHomotopy T
      (FrameHom.MixedNerve.homotopy (normalizedTensorElementEvaluation A X Y))) ?_ ?_
  · rfl
  · rw [FrameHom.MixedNerve.nerveMap_const, SSet.const_comp]
    have hv : T.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := A) Y := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (Complex A)).injective
      rfl
    exact congrArg SSet.const hv

lemma normalizedTensorEvaluationHomotopy_h :
    (normalizedTensorEvaluationHomotopy A X Y).h =
      (β_ (nerve (normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism _ ≫ normalizedTensorElementEvaluationJoin A X Y := by
  exact (normalizedTensorElementEvaluationJoin_prism A X Y).symm

end SerrePositivity.EInfinity.ComplexLimits
