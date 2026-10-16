module
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import Mathlib.Algebra.Algebra.Bilinear

/-! # Standard single algebra coefficients under actual restriction of scalars -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The restricted coefficient module has exactly the original R-algebra scalar action. -/
def algebraSelfRestrictionIso :
    (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B B) ≅ ModuleCat.of R B where
  hom := ConcreteCategory.ofHom (C := ModuleCat R)
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ (Algebra.smul_def (A := B) r x).symm }
  inv := ConcreteCategory.ofHom (C := ModuleCat R)
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ Algebra.smul_def (A := B) r x }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The standard coefficient comparison keeps every coefficient itself. -/
lemma algebraSelfRestrictionIso_hom_apply (b : B) :
    (algebraSelfRestrictionIso R B).hom b = b := rfl

/-- The original restricted derived single object is the original R-derived algebra module. -/
def algebraRestrictionSingleIso :
    (derivedRestrictScalars (algebraMap R B)).obj
        ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R B) :=
  (derivedRestrictScalarsSingleIso (algebraMap R B) 0).app (ModuleCat.of B B) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) 0).mapIso (algebraSelfRestrictionIso R B)

/-- The actual single-object comparison preserves multiplication by every coefficient. -/
lemma algebraRestrictionSingleIso_mul (b : B) :
    (derivedRestrictScalars (algebraMap R B)).map
        ((DerivedCategory.singleFunctor (ModuleCat B) 0).map
          (ModuleCat.ofHom (LinearMap.mulLeft B b))) ≫
      (algebraRestrictionSingleIso R B).hom =
    (algebraRestrictionSingleIso R B).hom ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.mulLeft R b)) := by
  let f := ModuleCat.ofHom (LinearMap.mulLeft B b)
  have hn := (derivedRestrictScalarsSingleIso (algebraMap R B) 0).hom.naturality f
  change (derivedRestrictScalars (algebraMap R B)).map
      ((DerivedCategory.singleFunctor (ModuleCat B) 0).map f) ≫
      (derivedRestrictScalarsSingleIso (algebraMap R B) 0).hom.app (ModuleCat.of B B) =
    (derivedRestrictScalarsSingleIso (algebraMap R B) 0).hom.app (ModuleCat.of B B) ≫
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map
        ((ModuleCat.restrictScalars (algebraMap R B)).map f) at hn
  simp only [algebraRestrictionSingleIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [reassoc_of% hn]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  have hm : (ModuleCat.restrictScalars (algebraMap R B)).map f ≫
        (algebraSelfRestrictionIso R B).hom =
      (algebraSelfRestrictionIso R B).hom ≫ ModuleCat.ofHom (LinearMap.mulLeft R b) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  rw [hm]
  rfl

end SerrePositivity
