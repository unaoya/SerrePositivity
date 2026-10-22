module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalDerivedHomMap
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoefficientYonedaSpaceIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.DerivedCoefficientMapping

/-! 元の係数の Yoneda 同型と元の導来比較の Hom 作用そのものから得る、一般宇宙の比較。 -/
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

def dgGluingCanonicalCoefficientDomainIso (c : C) (d : D) :
    (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).obj
      (complexPinchedSpace.{u, max u v w} (M.value c d)) ≅
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (DGNerve.pinchedHom R (RightModule R C) (representable R c) (M.rightAt d)) :=
  dgGluingComplexPinchedUniverseIso.{u, max u v w, max (u + 1) v} (M.value c d) ≪≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).mapIso
      (dgGluingCoefficientYonedaSpaceIso R C c (M.rightAt d))

def dgGluingCanonicalCoefficientTargetIso (c : C) (d : D) :=
  uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
      ((dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌)
        (Simplex.vertex (representable R c)))
      ((dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C))).app (Opposite.op ⦋0⦌)
        (Simplex.vertex (M.rightAt d))) ≪≫
    dgGluingDerivedCoefficientEndpointIso R C D M c d

def dgGluingCanonicalCoefficientMappingComparison (c : C) (d : D) :=
  (dgGluingCanonicalCoefficientDomainIso R C D M c d).hom ≫
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
      (pinchedHomMap (dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C)))
        (Simplex.vertex (representable R c)) (Simplex.vertex (M.rightAt d))) ≫
    (dgGluingCanonicalCoefficientTargetIso R C D M c d).hom

lemma dgGluingCanonicalCoefficientMappingComparison_equivalence (c : C) (d : D) :
    IsSimplicialHomotopyEquivalence
      (dgGluingCanonicalCoefficientMappingComparison R C D M c d) := by
  apply (dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingCanonicalCoefficientDomainIso R C D M c d) _).mpr
  apply (dgGluingHomotopyEquivalence_postcomp_iso_iff _
    (dgGluingCanonicalCoefficientTargetIso R C D M c d)).mpr
  exact (dgGluingModuleDerivedRepresentableHomMap_equivalence R C c (M.rightAt d)).ulift

lemma dgGluingCanonicalCoefficientMappingComparison_action (c : C) (d : D) :
    (dgGluingCanonicalCoefficientDomainIso R C D M c d).inv ≫
      dgGluingCanonicalCoefficientMappingComparison R C D M c d ≫
      (dgGluingCanonicalCoefficientTargetIso R C D M c d).inv =
    (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).map
      (pinchedHomMap (dgModuleResolvedInfinity R (RightModule R C) C
        (DGFunctor.id (RightModule R C)))
        (Simplex.vertex (representable R c)) (Simplex.vertex (M.rightAt d))) := by
  simp only [dgGluingCanonicalCoefficientMappingComparison, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]

lemma dgGluingCanonicalCoefficientMappingComparison_universe_action (c : C) (d : D) :
    (dgGluingCanonicalCoefficientDomainIso R C D M c d).inv ≫
      dgGluingCanonicalCoefficientMappingComparison R C D M c d ≫
      (dgGluingDerivedCoefficientEndpointIso R C D M c d).inv =
    (uliftPinchedHomIso.{max (u + 1) v, max (u + 1) v w}
      (C := dgNerve R (RightModule R C))
      (Simplex.vertex (representable R c)) (Simplex.vertex (M.rightAt d))).hom ≫
      pinchedHomMap (dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
        (ULift.up (Simplex.vertex (representable R c)))
        (ULift.up (Simplex.vertex (M.rightAt d))) := by
  simp only [dgGluingCanonicalCoefficientMappingComparison,
    dgGluingCanonicalCoefficientTargetIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact uliftPinchedHomIso_naturality
    (dgModuleResolvedInfinity R (RightModule R C) C (DGFunctor.id (RightModule R C)))
    (Simplex.vertex (representable R c)) (Simplex.vertex (M.rightAt d))

end SerrePositivity.InfinityCategories
