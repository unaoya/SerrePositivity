module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChangeScalar
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorCoefficient
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle

/-! # Original new-base H⁰ modules and the completed tensor coefficient algebra -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

/-- Normalize the original restricted scalar factor without changing its elements. -/
def baseChangeScalarNormalizationIso :
    derivedBaseChangeScalarObject (algebraMap R S) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S) :=
  boundedAboveDerivedSingleFunctor.mapIso (algebraSelfRestrictionIso R S)

lemma baseChangeScalarNormalizationIso_scalar (s : S) :
    (show derivedBaseChangeScalarObject (algebraMap R S) ⟶
      derivedBaseChangeScalarObject (algebraMap R S) from
      boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication (algebraMap R S) s)) ≫
        (baseChangeScalarNormalizationIso R S).hom =
      (baseChangeScalarNormalizationIso R S).hom ≫
        boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)) := by
  have h : restrictedScalarMultiplication (algebraMap R S) s ≫
      (algebraSelfRestrictionIso R S).hom =
    (algebraSelfRestrictionIso R S).hom ≫ ModuleCat.ofHom (LinearMap.mulLeft R s) := by
    ext x
    rfl
  change boundedAboveDerivedSingleFunctor.map _ ≫ boundedAboveDerivedSingleFunctor.map _ =
    boundedAboveDerivedSingleFunctor.map _ ≫ boundedAboveDerivedSingleFunctor.map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

variable (a : R)

/-- The actual tensor normalization retains the original scalar factor. -/
def completedScalarTensorNormalizationIso :
    (boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj
          (derivedBaseChangeScalarObject (algebraMap R S),
            boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))) ≅
      (boundedAboveCompletedTensorAlgebra R a S T).X :=
  (boundedAboveDerivedCompletionFunctor R a).mapIso
    (boundedAboveDerivedTensor.mapIso
      (Iso.prod (baseChangeScalarNormalizationIso R S)
        (Iso.refl (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))))

lemma completedScalarTensorNormalizationIso_scalar (s : S) :
    (boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
      (CategoryTheory.Prod.mkHom
        (show derivedBaseChangeScalarObject (algebraMap R S) ⟶
          derivedBaseChangeScalarObject (algebraMap R S) from
          boundedAboveDerivedSingleFunctor.map
            (restrictedScalarMultiplication (algebraMap R S) s))
        (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))))) ≫
      (completedScalarTensorNormalizationIso R S T a).hom =
    (completedScalarTensorNormalizationIso R S T a).hom ≫
      (boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
        (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R s)))
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T))))) := by
  simp only [completedScalarTensorNormalizationIso, Functor.mapIso_hom, Iso.prod_hom,
    Iso.refl_hom]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  congr 1
  apply CategoryTheory.Prod.hom_ext
  · exact baseChangeScalarNormalizationIso_scalar R S s
  · simp

/-- Original S-homology, after restriction, compared to the original completed tensor H⁰. -/
def completedBaseChangeTensorH0Iso :
    (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
          ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
            ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
              (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj) ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R a S T).X.obj :=
  completedBaseChangeTensorRestrictionHomologyIso (algebraMap R S) a
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)) 0 ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (completedScalarTensorNormalizationIso R S T a))

/-- Every original S-scalar is preserved, for the original left-factor algebra action. -/
lemma completedBaseChangeTensorH0Iso_smul (s : S)
    (x : (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    (completedBaseChangeTensorH0Iso R S T a).hom (s • x) =
      s • (completedBaseChangeTensorH0Iso R S T a).hom x := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  have hn := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
    (congrArg (fun f => f.hom) (completedScalarTensorNormalizationIso_scalar R S T a s))
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hn
  have hx := completedBaseChangeTensorRestrictionHomologyIso_scalar (algebraMap R S) a
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)) 0 s x
  simp only [completedBaseChangeTensorH0Iso, Iso.trans_hom, Functor.mapIso_hom,
    ModuleCat.comp_apply]
  change _ = s • _
  rw [hx]
  have hp := congrArg (fun f => f.hom
    ((completedBaseChangeTensorRestrictionHomologyIso (algebraMap R S) a
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)) 0).hom x)) hn
  exact hp.trans (completedTensorH0_left_coefficient_smul R a S T s _)

/-- The comparison is S-linear for the original source and original factor algebra target. -/
def completedBaseChangeTensorH0LinearEquiv :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj ≃ₗ[S]
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
  letI := completedTensorH0LeftAlgebra R a S T
  exact { (completedBaseChangeTensorH0Iso R S T a).toLinearEquiv.toAddEquiv with
    map_smul' := completedBaseChangeTensorH0Iso_smul R S T a }

/-- The S-linear equivalence is precisely the original restricted H⁰ comparison. -/
lemma completedBaseChangeTensorH0LinearEquiv_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
      ((boundedAboveDerivedCompletionFunctor S (algebraMap R S a)).obj
        ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)))).obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R a S T)
    letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R a S T)
    letI := completedTensorH0LeftAlgebra R a S T
    completedBaseChangeTensorH0LinearEquiv R S T a x =
      (completedBaseChangeTensorH0Iso R S T a).hom x := rfl

end SerrePositivity.DerivedCompletion
