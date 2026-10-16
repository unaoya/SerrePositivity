module
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.CochainTensorBaseChange
public import SerrePositivity.HomologicalAlgebra.CochainTensorShuffle
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedTensor
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! # The actual derived tensor and completion under a ring equivalence -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

/-- Restriction along a ring equivalence commutes with the full tensor complex. -/
def cochainTensorRingEquivRestrictionIso (P Q : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (cochainTensor P Q) ≅
      cochainTensor
        (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q) :=
  let h := NatIso.mapHomologicalComplex (restrictScalarsIsoExtendInverse e) (.up ℤ)
  h.app (cochainTensor P Q) ≪≫ cochainTensorBaseChangeIso e.symm.toRingHom P Q ≪≫
    cochainTensorIso (h.symm.app P) (h.symm.app Q)

/-- The original restricted projective complex represents the original restricted derived object. -/
def ringEquivRestrictedDerivedModel (X : DerivedCategory.Minus (ModuleCat.{u} S))
    (P : BoundedAboveDerivedModel X.obj) :
    BoundedAboveDerivedModel ((boundedAboveDerivedRestrictScalars e.toRingHom).obj X).obj where
  complex := ((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj P.complex
  bound := P.bound
  bounded := inferInstance
  projective i :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).toAdjunction.map_projective
      (P.complex.X i) (P.projective i)
  iso := (boundedAboveDerivedRestrictScalarsModelIso e.toRingHom X P).symm

/-- Compare the actual tensors, using the same restricted projective models in both variables. -/
def boundedAboveDerivedTensorRingEquivRestrictionIso
    (X Y : DerivedCategory.Minus (ModuleCat.{u} S)) :
    (boundedAboveDerivedRestrictScalars e.toRingHom).obj (boundedAboveDerivedTensor.obj (X, Y)) ≅
      boundedAboveDerivedTensor.obj
        ((boundedAboveDerivedRestrictScalars e.toRingHom).obj X,
          (boundedAboveDerivedRestrictScalars e.toRingHom).obj Y) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let h : ((boundedAboveDerivedRestrictScalars e.toRingHom).obj
      (boundedAboveDerivedTensor.obj (X, Y))).obj ≅
      DerivedCategory.Q.obj (cochainTensor
        (ringEquivRestrictedDerivedModel e X P).complex
        (ringEquivRestrictedDerivedModel e Y Q).complex) :=
    (derivedRestrictScalars e.toRingHom).mapIso (boundedAboveDerivedTensorModelIso X Y P Q) ≪≫
      (derivedRestrictScalarsFactors e.toRingHom).app (cochainTensor P.complex Q.complex) ≪≫
      DerivedCategory.Q.mapIso (cochainTensorRingEquivRestrictionIso e P.complex Q.complex)
  exact ObjectProperty.isoMk _ (h ≪≫
    (boundedAboveDerivedTensorModelIso _ _
      (ringEquivRestrictedDerivedModel e X P) (ringEquivRestrictedDerivedModel e Y Q)).symm)

/-- The original completion after tensor also commutes with restriction along the equivalence. -/
def boundedAboveCompletedTensorRingEquivRestrictionIso (a : R)
    (X Y : DerivedCategory.Minus (ModuleCat.{u} S)) :
    (boundedAboveDerivedRestrictScalars e.toRingHom).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor S (e a)).obj
          (boundedAboveDerivedTensor.obj (X, Y))) ≅
      (DerivedCompletion.boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          ((boundedAboveDerivedRestrictScalars e.toRingHom).obj X,
            (boundedAboveDerivedRestrictScalars e.toRingHom).obj Y)) :=
  ((DerivedCompletion.boundedAboveCompletionRestrictionIso e.toRingHom a).app
    (boundedAboveDerivedTensor.obj (X, Y))).symm ≪≫
      (DerivedCompletion.boundedAboveDerivedCompletionFunctor R a).mapIso
        (boundedAboveDerivedTensorRingEquivRestrictionIso e X Y)

/-- The comparison preserves the original completion units. -/
lemma boundedAboveCompletedTensorRingEquivRestrictionIso_unit (a : R)
    (X Y : DerivedCategory.Minus (ModuleCat.{u} S)) :
    (boundedAboveDerivedRestrictScalars e.toRingHom).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit S (e a)).app
          (boundedAboveDerivedTensor.obj (X, Y))) ≫
        (boundedAboveCompletedTensorRingEquivRestrictionIso e a X Y).hom =
      (DerivedCompletion.boundedAboveDerivedCompletionUnit R a).app
          ((boundedAboveDerivedRestrictScalars e.toRingHom).obj
            (boundedAboveDerivedTensor.obj (X, Y))) ≫
        (DerivedCompletion.boundedAboveDerivedCompletionFunctor R a).map
          (boundedAboveDerivedTensorRingEquivRestrictionIso e X Y).hom := by
  let Z := boundedAboveDerivedTensor.obj (X, Y)
  let c := (DerivedCompletion.boundedAboveCompletionRestrictionIso e.toRingHom a).app Z
  have h := congrArg (fun f => f ≫ c.inv)
    (DerivedCompletion.boundedAboveCompletionRestrictionIso_unit e.toRingHom a Z)
  change ((DerivedCompletion.boundedAboveDerivedCompletionUnit R a).app
    ((boundedAboveDerivedRestrictScalars e.toRingHom).obj Z) ≫ c.hom) ≫ c.inv = _ at h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  change _ ≫ (c.inv ≫ _) = _
  rw [← Category.assoc]
  exact congrArg (fun f => f ≫
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor R a).map
      (boundedAboveDerivedTensorRingEquivRestrictionIso e X Y).hom) h.symm

/-- The original derived single object has the original restricted module as its coefficient. -/
def boundedAboveRestrictionSingleIso (φ : R →+* S) (M : ModuleCat.{u} S) :
    (boundedAboveDerivedRestrictScalars φ).obj (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj ((ModuleCat.restrictScalars φ).obj M) :=
  ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso φ 0).app M)

/-- The completed derived tensor comparison for the original two coefficient modules. -/
def completedTensorModulesRingEquivRestrictionIso (a : R) (M N : ModuleCat.{u} S) :
    (boundedAboveDerivedRestrictScalars e.toRingHom).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor S (e a)).obj
          (boundedAboveDerivedTensor.obj
            (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))) ≅
      (DerivedCompletion.boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          (boundedAboveDerivedSingleFunctor.obj ((ModuleCat.restrictScalars e.toRingHom).obj M),
            boundedAboveDerivedSingleFunctor.obj
              ((ModuleCat.restrictScalars e.toRingHom).obj N))) :=
  boundedAboveCompletedTensorRingEquivRestrictionIso e a _ _ ≪≫
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor R a).mapIso
      (boundedAboveDerivedTensor.mapIso (Iso.prod
        (boundedAboveRestrictionSingleIso e.toRingHom M)
        (boundedAboveRestrictionSingleIso e.toRingHom N)))

/-- Arbitrary restriction reflects homology vanishing, retaining the underlying abelian group. -/
lemma derivedRestrictScalars_homology_isZero_iff (φ : R →+* S)
    (X : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj
      ((derivedRestrictScalars φ).obj X)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat S) n).obj X) := by
  exact ((derivedRestrictScalarsHomologyIso φ n).app X).isZero_iff.trans (by
    simp only [ModuleCat.isZero_iff_subsingleton]
    rfl)

/-- The lower cohomological bound is equivalent before and after arbitrary restriction. -/
lemma derivedRestrictScalars_isGE_iff (φ : R →+* S)
    (X : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    ((derivedRestrictScalars φ).obj X).IsGE n ↔ X.IsGE n := by
  rw [DerivedCategory.isGE_iff, DerivedCategory.isGE_iff]
  simp only [derivedRestrictScalars_homology_isZero_iff]

/-- The upper cohomological bound is equivalent before and after arbitrary restriction. -/
lemma derivedRestrictScalars_isLE_iff (φ : R →+* S)
    (X : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    ((derivedRestrictScalars φ).obj X).IsLE n ↔ X.IsLE n := by
  rw [DerivedCategory.isLE_iff, DerivedCategory.isLE_iff]
  simp only [derivedRestrictScalars_homology_isZero_iff]

/-- A compatible algebra presentation identifies the original restricted coefficient module. -/
def ringEquivAlgebraRestrictionModuleIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (eA : A ≃+* B)
    (h : eA.toRingHom.comp (algebraMap R A) = (algebraMap S B).comp e.toRingHom) :
    (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S B) ≅ ModuleCat.of R A := by
  letI : Module R B := Module.compHom B e.toRingHom
  exact
    { hom := ModuleCat.ofHom
        { toFun := fun x => eA.symm x
          map_add' := eA.symm.map_add
          map_smul' := fun r x => by
            apply eA.injective
            change eA (eA.symm ((e r) • x)) = eA (r • eA.symm x)
            simp only [Algebra.smul_def, eA.apply_symm_apply, map_mul]
            exact congrArg (fun z => z * x) (RingHom.congr_fun h r).symm }
      inv := ModuleCat.ofHom
        { toFun := fun x => eA x
          map_add' := eA.map_add
          map_smul' := fun r x => by
            change eA (r • x) = (e r) • eA x
            simp only [Algebra.smul_def, map_mul]
            exact congrArg (fun z => z * eA x) (RingHom.congr_fun h r) }
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact eA.apply_symm_apply x
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact eA.symm_apply_apply x }

/-- Vanishing in every degree is equivalent for the original completed module tensors. -/
lemma completedTensorModulesRingEquivRestriction_homology_isZero_iff
    (a : R) (M N : ModuleCat.{u} S) (n : ℤ) :
    let X := (DerivedCompletion.boundedAboveDerivedCompletionFunctor S (e a)).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N))
    let Y := (DerivedCompletion.boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj ((ModuleCat.restrictScalars e.toRingHom).obj M),
          boundedAboveDerivedSingleFunctor.obj ((ModuleCat.restrictScalars e.toRingHom).obj N)))
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat S) n).obj X.obj) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj Y.obj) := by
  exact (derivedRestrictScalars_homology_isZero_iff e.toRingHom _ n).symm.trans
    (((DerivedCategory.homologyFunctor (ModuleCat R) n).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (completedTensorModulesRingEquivRestrictionIso e a M N))).isZero_iff)

end SerrePositivity
