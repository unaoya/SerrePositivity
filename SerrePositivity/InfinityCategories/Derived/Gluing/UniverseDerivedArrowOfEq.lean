module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedArrowRepresentation
public import SerrePositivity.InfinityCategories.Derived.Gluing.EdgeEndpointTransport

/-! 指定端点への等式輸送を含む、同じ実導来矢印の閉射表示。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

lemma dgGluingUniverseDerivedArrow_representation_of_eq (N P : RightModule R C)
    (hN : moduleHomotopicallyProjective R C (ForgetEnrichment.of (Complex R) N))
    {x y : ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)) _⦋0⦌}
    (hx : (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex N)) = x)
    (hy : (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex P)) = y)
    (α : ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)).Edge x y) :
    ∃ a : ForgetEnrichment.of (Complex R) N ⟶ ForgetEnrichment.of (Complex R) P,
      Nonempty (VertexIso
        (intervalMappingVertexOfEdge (dgGluingEdgeEndpointTransport hx hy
          ((Edge.ofTruncated (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v w}
            (X := dgNerve R (RightModule R C)) (dgClosedEdge R (RightModule R C) a))).map
              (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C))))
        (intervalMappingVertexOfEdge α)) := by
  subst x
  subst y
  exact dgGluingUniverseDerivedArrow_representation R C N P hN α

end SerrePositivity.InfinityCategories
