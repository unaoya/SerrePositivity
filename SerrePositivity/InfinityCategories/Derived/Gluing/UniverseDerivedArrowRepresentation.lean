module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedHomMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.EdgeRepresentation
public import SerrePositivity.InfinityCategories.Derived.Gluing.ClosedArrowOfULiftEdge
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration

/-! gluing の共通宇宙の任意の導来矢印を、元の閉加群射で端点固定に表す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseDerivedArrow_representation (N P : RightModule R C)
    (hN : moduleHomotopicallyProjective R C (ForgetEnrichment.of (Complex R) N))
    (α : ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C)).Edge
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex N)))
      ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex P)))) :
    ∃ a : ForgetEnrichment.of (Complex R) N ⟶ ForgetEnrichment.of (Complex R) P,
      Nonempty (VertexIso
        (intervalMappingVertexOfEdge ((Edge.ofTruncated
          (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v w}
            (X := dgNerve R (RightModule R C))
            (dgClosedEdge R (RightModule R C) a))).map
              (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)))
        (intervalMappingVertexOfEdge α)) := by
  obtain ⟨b, he⟩ := dgGluingEdgeRepresentation_of_hom_equivalence
    (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
    (ULift.up (Simplex.vertex N)) (ULift.up (Simplex.vertex P))
    (dgGluingUniverseModuleDerivedHomMap_equivalence R C N P hN) α
  obtain ⟨a, ha⟩ := dgGluingClosedArrowOfULiftEdge.{u, max (u + 1) v, max (u + 1) v w}
    R (RightModule R C) N P b
  refine ⟨a, ?_⟩
  rw [ha]
  exact he

end SerrePositivity.InfinityCategories
