module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleFrontMap
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTriangleRightMaps
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorEvaluationHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.HomotopyTriangleClasses
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison
/-! 概要：元の大域評価三角形は全関手圏内で同じ全族の合成を与える。
方針：元の全三辺を持つ二単体族を curry する。
規約：全 K と元の円柱を保持。使われ方：同じ導来 roof との大域比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.SimplicialModel
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)
lemma normalizedTensorTriangleFamily_comp :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorConeFamilyHom A X Y ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationHomotopy A X Y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y)) := by
  let K := nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A X Y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (Complex A))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y))
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyTriangle_homMk_comp (_root_.SerrePositivity.ComplexLimits.normalizedTensorConeHomotopy A X Y)
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationHomotopy A X Y) H
    ((β_ K (Δ[2] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleMap A X Y)
  · have hn : (K ◁ SSet.stdSimplex.δ (2 : Fin 3)) ≫ (β_ K (Δ[2] : SSet.{u + 1})).hom =
        (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ (SSet.stdSimplex.δ (2 : Fin 3) ▷ K) := rfl
    rw [← Category.assoc, hn, Category.assoc]
    exact congrArg (fun f => (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ f)
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleMap_face01 A X Y)
  · have hn : (K ◁ SSet.stdSimplex.δ (0 : Fin 3)) ≫ (β_ K (Δ[2] : SSet.{u + 1})).hom =
        (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ (SSet.stdSimplex.δ (0 : Fin 3) ▷ K) := rfl
    rw [← Category.assoc, hn, Category.assoc]
    exact (congrArg (fun f => (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ f)
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleMap_face12 A X Y)).trans
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorEvaluationHomotopy_h A X Y).symm
  · have hn : (K ◁ SSet.stdSimplex.δ (1 : Fin 3)) ≫ (β_ K (Δ[2] : SSet.{u + 1})).hom =
        (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ (SSet.stdSimplex.δ (1 : Fin 3) ▷ K) := rfl
    rw [← Category.assoc, hn, Category.assoc]
    apply Eq.trans (congrArg (fun f => (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ f)
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorTriangleMap_face02 A X Y))
    change _ = (β_ K (Δ[1] : SSet.{u + 1})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry]
end SerrePositivity.ComplexLimits
