module
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionSingleH0
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraScalarAction

/-! # The original completion restriction comparison preserves standard coefficient classes -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The original R-algebra single comparison is normalized on its actual H⁰. -/
lemma algebraRestrictionSingleIso_homology :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (algebraRestrictionSingleIso R B).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app
        (ModuleCat.of R B) =
    (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)) ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).hom.app
          (ModuleCat.of B B)) ≫ (algebraSelfRestrictionIso R B).hom := by
  simp only [algebraRestrictionSingleIso, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.naturality
    (algebraSelfRestrictionIso R B).hom
  simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] at hn
  rw [hn, ← Category.assoc]
  erw [derivedRestrictionSingleH0_normalization]
  rfl

/-- The inverse comparison sends each original standard R class to its original B class. -/
lemma algebraRestrictionSingleIso_inv_homology :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R B) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (algebraRestrictionSingleIso R B).inv ≫
      (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)) =
    (algebraSelfRestrictionIso R B).inv ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
          (ModuleCat.of B B)) := by
  have h := congrArg (fun f ↦
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R B) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (algebraRestrictionSingleIso R B).inv ≫ f ≫
      (algebraSelfRestrictionIso R B).inv ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
          (ModuleCat.of B B))) (algebraRestrictionSingleIso_homology R B)
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

namespace DerivedCompletion
variable (a : R)

/-- The actual completed H⁰ comparison preserves the original maps from the coefficient module. -/
lemma completedAlgebraRestrictionH0Iso_unit_map :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R B) ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((derivedComplexCompletionUnit R a).app
          ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R B))) ≫
      (completedAlgebraRestrictionH0Iso R a B).hom =
    (algebraSelfRestrictionIso R B).inv ≫
      (ModuleCat.restrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat B) 0).inv.app
          (ModuleCat.of B B) ≫
        (DerivedCategory.homologyFunctor (ModuleCat B) 0).map
          ((derivedComplexCompletionUnit B (algebraMap R B a)).app
            ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)))) := by
  simp only [completedAlgebraRestrictionH0Iso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← CategoryTheory.Functor.map_comp_assoc, completedAlgebraRestrictionIso_unit,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (derivedRestrictScalarsHomologyIso (algebraMap R B) 0).hom.naturality
    ((derivedComplexCompletionUnit B (algebraMap R B a)).app
      ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)))
  simp only [CategoryTheory.Functor.comp_map] at hn
  erw [hn, ← Category.assoc, ← Category.assoc, algebraRestrictionSingleIso_inv_homology]
  rw [Category.assoc, CategoryTheory.Functor.map_comp]

/-- Every standard coefficient class is preserved by the actual completed comparison. -/
lemma completedAlgebraRestrictionH0Iso_unit (b : B) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    letI := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
    letI := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
    (completedAlgebraRestrictionH0Iso R a B).hom (completedAlgebraUnitAlgHom R a B b) =
      completedAlgebraUnitAlgHom B (algebraMap R B a) B b := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
  let := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
  rw [completedAlgebraUnitAlgHom_apply, completedAlgebraUnitAlgHom_apply,
    completionH0AlgebraUnit_apply, completionH0AlgebraUnit_apply]
  exact congrArg (fun f ↦ f.hom b) (completedAlgebraRestrictionH0Iso_unit_map R B a)

/-- In particular the original comparison carries the actual H⁰ ring unit to the actual unit. -/
lemma completedAlgebraRestrictionH0Iso_one :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
    (completedAlgebraRestrictionH0Iso R a B).hom 1 =
      (1 : (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
        (completedUnitAlgebra B (algebraMap R B a)).X.obj) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
  let := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
  simpa only [map_one] using completedAlgebraRestrictionH0Iso_unit R B a 1

end DerivedCompletion
end SerrePositivity
