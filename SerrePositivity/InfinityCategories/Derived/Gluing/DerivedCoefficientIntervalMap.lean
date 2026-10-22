module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PinchedIntervalEndpointTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedHomCoefficientPath

/-! 主比較と同じ導来端点における pinched Hom から区間 Hom への実同値。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

def dgGluingDerivedCoefficientIntervalMap (c : C) (d : D) :=
  pinchedHomToIntervalMappingSpace
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex c)))
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (DGNerve.Simplex.vertex d)))

lemma dgGluingDerivedCoefficientIntervalMap_equivalence (c : C) (d : D) :
    IsSimplicialHomotopyEquivalence (dgGluingDerivedCoefficientIntervalMap R C D M c d) :=
  (pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).isSimplicialHomotopyEquivalence

lemma dgGluingDerivedCoefficientIntervalMap_uncurry {T : SSet.{max (u + 1) v w}}
    (c : C) (d : D)
    (f : T ⟶ InfinityCategories.pinchedHom
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex c)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (DGNerve.Simplex.vertex d)))) :
    intervalMappingUncurry (f ≫ dgGluingDerivedCoefficientIntervalMap R C D M c d) =
      intervalMappingUncurry (f ≫ (dgGluingDerivedCoefficientEndpointIso R C D M c d).inv ≫
        pinchedHomToIntervalMappingSpace _ _) :=
  (dgGluingPinchedIntervalEndpointTransport_uncurry
    (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C c).symm
    (dgGluingUniverseDerivedCoefficient_vertex R C D M d).symm f).symm

end SerrePositivity.InfinityCategories
