module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalHomMapCriterion
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalDerivedHomMap
public import SerrePositivity.InfinityCategories.Derived.DGClosedEdges
public import SerrePositivity.InfinityCategories.F1.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.EdgeRepresentation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedArrowOfEdge

/-! 射影的始域からの任意の実導来矢印を、元の閉加群射の像と端点固定で同型にする。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
local notation "L" => dgModuleResolvedInfinity R (RightModule R C) C
  (DGFunctor.id (RightModule R C))

lemma dgGluingDerivedArrow_representation (N P : RightModule R C)
    (hN : moduleHomotopicallyProjective R C (ForgetEnrichment.of (Complex R) N))
    (α : (dgModuleDerivedInfinityCategory R C).Edge
      ((L).app (Opposite.op ⦋0⦌) (Simplex.vertex N))
      ((L).app (Opposite.op ⦋0⦌) (Simplex.vertex P))) :
    ∃ a : ForgetEnrichment.of (Complex R) N ⟶ ForgetEnrichment.of (Complex R) P,
      Nonempty (VertexIso
        (intervalMappingVertexOfEdge
          ((Edge.ofTruncated (dgClosedEdge R (RightModule R C) a)).map L))
        (intervalMappingVertexOfEdge α)) := by
  obtain ⟨b, he⟩ := dgGluingEdgeRepresentation_of_hom_equivalence L
    (Simplex.vertex N) (Simplex.vertex P)
    (dgGluingModuleDerivedHomMap_equivalence R C N P hN)
    α
  obtain ⟨a, ha⟩ := dgGluingClosedArrowOfEdge R (RightModule R C) N P b
  refine ⟨a, ?_⟩
  rw [ha]
  exact he

end SerrePositivity.InfinityCategories
