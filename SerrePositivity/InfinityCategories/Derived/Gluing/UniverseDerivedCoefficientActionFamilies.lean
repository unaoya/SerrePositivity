module
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniverseModuleDerivedFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.CanonicalCoefficientMapping

/-! 元の二作用の導来区間族を、canonical な係数比較と厳密に照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingUniverseModuleDerivedFamilyInterval_coefficient {A : Complex R}
    (c : C) (d : D) (a : A ⟶ M.value c d) :
    dgGluingUniverseModuleDerivedFamilyInterval.{u, v, w} R C
        (complexPinchedMap.{u, max (u + 1) v} a ≫
          (dgGluingCoefficientYonedaSpaceIso R C c (M.rightAt d)).hom) =
      (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} a) ≫
        dgGluingCanonicalCoefficientMappingComparison R C D M c d ≫
          (dgGluingDerivedCoefficientEndpointIso R C D M c d).inv ≫
            pinchedHomToIntervalMappingSpace _ _ := by
  simp only [dgGluingUniverseModuleDerivedFamilyInterval,
    dgGluingCanonicalCoefficientMappingComparison, dgGluingCanonicalCoefficientDomainIso,
    dgGluingCanonicalCoefficientTargetIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    ((SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
      (complexPinchedMap.{u, max u v w} a)), dgGluingComplexPinchedUniverseIso_naturality a]
  simp only [Category.assoc]
  rfl

end SerrePositivity.InfinityCategories
