module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedArrowRepresentation
public import SerrePositivity.InfinityCategories.Derived.Gluing.EdgeEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientMapping
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseDerivedArrowOfEq

/-! gluing の実二脚を端点とする導来矢印を、元の閉加群射の像で表す。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedModuleArrow (c : C) (d : D)
    (a : ForgetEnrichment.of (Complex R) (representable R c) ⟶
      ForgetEnrichment.of (Complex R) (M.rightAt d)) :=
  dgGluingEdgeEndpointTransport
    (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C c).symm
    (dgGluingUniverseDerivedCoefficient_vertex R C D M d).symm
    ((Edge.ofTruncated (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v w}
      (X := dgNerve R (RightModule R C)) (dgClosedEdge R (RightModule R C) a))).map
      (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C))

lemma dgGluingDerivedModuleArrow_representation (c : C) (d : D)
    (α : ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)).Edge
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex c)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex d)))) :
    ∃ a : ForgetEnrichment.of (Complex R) (representable R c) ⟶
        ForgetEnrichment.of (Complex R) (M.rightAt d),
      Nonempty (VertexIso (intervalMappingVertexOfEdge (dgGluingDerivedModuleArrow R C D M c d a))
        (intervalMappingVertexOfEdge α)) := by
  exact dgGluingUniverseDerivedArrow_representation_of_eq R C (representable R c) (M.rightAt d)
    (representable_homotopicallyProjective R C c)
    (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C c).symm
    (dgGluingUniverseDerivedCoefficient_vertex R C D M d).symm α

end SerrePositivity.InfinityCategories
