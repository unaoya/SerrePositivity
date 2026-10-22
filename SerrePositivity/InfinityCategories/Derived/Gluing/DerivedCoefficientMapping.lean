module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseCoefficientAugmentationSquare

/-! 二つの gluing 射影が指定する実導来端点間の Hom への係数比較。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseDerivedYoneda_vertex (c : C) :
    (dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex c)) =
      (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex (representable R c))) := by
  change (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
    ((dgGluingUniverseYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex c))) = _
  apply congrArg ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app
    (Opposite.op ⦋0⦌))
  exact dgGluingUniverseNerveMap_vertex.{u, v, max (u + 1) v, max (u + 1) v w}
    (dgYoneda R C) c

lemma dgGluingUniverseDerivedCoefficient_vertex (d : D) :
    (dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex d)) =
      (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex (M.rightAt d))) := by
  change (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app (Opposite.op ⦋0⦌)
    ((dgGluingUniverseCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex d))) = _
  apply congrArg ((dgGluingUniverseModuleDerivedComparison.{u, v, w} R C).app
    (Opposite.op ⦋0⦌))
  exact dgGluingUniverseNerveMap_vertex.{u, w, max (u + 1) v, max (u + 1) v w}
    M.toFunctor d

def dgGluingDerivedCoefficientEndpointIso (c : C) (d : D) :=
  pinchedEndpointIso (dgGluingUniverseDerivedYoneda_vertex.{u, v, w} R C c).symm
    (dgGluingUniverseDerivedCoefficient_vertex R C D M d).symm

def dgGluingDerivedCoefficientMappingComparison (c : C) (d : D) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w}
        ((dgGluingResolvedModule R C (M.rightAt d)).val.obj (Opposite.op c))) ⟶
    InfinityCategories.pinchedHom
      (X := (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (dgModuleDerivedInfinityCategory R C))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex c)))
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (Simplex.vertex d))) :=
  dgGluingUniverseResolvedCoefficientHomComparison.{u, v, w} R C c (M.rightAt d) ≫
    (dgGluingDerivedCoefficientEndpointIso R C D M c d).hom

lemma dgGluingDerivedCoefficientMappingComparison_equivalence (c : C) (d : D) :
    IsSimplicialHomotopyEquivalence (dgGluingDerivedCoefficientMappingComparison R C D M c d) :=
  (dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (dgGluingDerivedCoefficientEndpointIso R C D M c d)).mpr
      (dgGluingUniverseResolvedCoefficientHomComparison_equivalence R C c (M.rightAt d))

lemma dgGluingDerivedCoefficientMappingComparison_augmentation (c : C) (d : D) :
    dgGluingDerivedCoefficientMappingComparison R C D M c d ≫
      (dgGluingDerivedCoefficientEndpointIso R C D M c d).inv ≫
      dgGluingUniverseDerivedCoefficientHomSpanLeft.{u, v, w} R C c (M.rightAt d) =
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
        (complexPinchedMap.{u, max u v w}
          (dgGluingResolvedCoefficientEvaluation R C c (M.rightAt d))) ≫
      dgGluingUniverseDerivedCoefficientHomSpanRight.{u, v, w} R C c (M.rightAt d) := by
  rw [dgGluingDerivedCoefficientMappingComparison, Category.assoc,
    Iso.hom_inv_id_assoc, dgGluingUniverseResolvedCoefficientHomComparison_augmentation]

end SerrePositivity.InfinityCategories
