module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedArrowRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.EdgeEndpointTransport

/-! 指定端点への等式輸送を含む、同じ実導来矢印の閉射表示。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseDerivedArrow_representation_of_eq (N P : _root_.SerrePositivity.DifferentialGraded.RightModule R C)
    (hN : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R C (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N))
    {x y : ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C)) _⦋0⦌}
    (hx : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)) = x)
    (hy : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex P)) = y)
    (α : ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R C)).Edge x y) :
    ∃ a : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) P,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingEdgeEndpointTransport hx hy
          ((Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v w}
            (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R C)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R (RightModule R C) a))).map
              (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C))))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge α)) := by
  subst x
  subst y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedArrow_representation R C N P hN α

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
