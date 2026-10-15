module
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.LinearFunctorScalarCone
public import SerrePositivity.HomologicalAlgebra.CochainConeAdditiveNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion

/-! # Restriction of coefficients for the actual power-Koszul completion stages -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
open HomologicalComplex.homotopyCofiber
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Restriction sends the actual scalar endomorphism to its original base-ring scalar. -/
lemma restrictCochain_smulId (a : R) (b : S) (hab : φ a = b)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map (smulId b K) =
      smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  subst b
  rfl

/-- The canonical additive cone comparison preserves the specified scalar after restriction. -/
def restrictionScalarConeIso (a : R) (b : S) (hab : φ a = b)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone (smulId b K)) ≅
      CochainComplex.mappingCone (smulId a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) :=
  additiveFunctorCofiberIsoOfEq (ModuleCat.restrictScalars φ) (smulId b K) _
    (restrictCochain_smulId φ a b hab K)

/-- The inverse scalar-cone comparison preserves the original first component inclusion. -/
@[reassoc] lemma restrictionScalarConeIso_inv_inl
    (a : R) (b : S) (hab : φ a = b) (K : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    inlX (smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K))
        (i + 1) i rfl ≫ (restrictionScalarConeIso φ a b hab K).inv.f i =
      (ModuleCat.restrictScalars φ).map (inlX (smulId b K) (i + 1) i rfl) :=
  additiveFunctorCofiberIsoOfEq_inv_inl _ _ _ _ _

/-- The inverse comparison also preserves the original second component inclusion. -/
@[reassoc] lemma restrictionScalarConeIso_inv_inr
    (a : R) (b : S) (hab : φ a = b) (K : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    inrX (smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) i ≫
        (restrictionScalarConeIso φ a b hab K).inv.f i =
      (ModuleCat.restrictScalars φ).map (inrX (smulId b K) i) :=
  additiveFunctorCofiberIsoOfEq_inv_inr _ _ _ _ _

/-- Restriction compares the actual power-Koszul stages for every natural power. -/
def restrictionPowerKoszulStageIso (a : R)
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
        (complexPowerKoszulStage S (φ a) K n) ≅
      complexPowerKoszulStage R a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n :=
  restrictionScalarConeIso φ (a ^ n) ((φ a) ^ n) (map_pow φ a n) K

/-- The inverse comparison is natural in every actual coefficient-complex morphism. -/
@[reassoc] lemma restrictionScalarConeIso_inv_naturality
    (a : R) (b : S) (hab : φ a = b)
    {K L : CochainComplex (ModuleCat.{u} S) ℤ} (f : K ⟶ L) :
    (restrictionScalarConeIso φ a b hab K).inv ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
          ((scalarConeFunctor b).map f) =
      (scalarConeFunctor a).map
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f) ≫
        (restrictionScalarConeIso φ a b hab L).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ext_from_X
    (smulId a (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K))
    (i + 1) i rfl
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      scalarConeFunctor_inl_map_assoc]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inl,
      ← CategoryTheory.Functor.map_comp, scalarConeFunctor_inl_map,
      CategoryTheory.Functor.map_comp, restrictionScalarConeIso_inv_inl]
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      scalarConeFunctor_inr_map_assoc]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inr,
      ← CategoryTheory.Functor.map_comp, scalarConeFunctor_inr_map,
      CategoryTheory.Functor.map_comp, restrictionScalarConeIso_inv_inr]

/-- The standard inclusion into a scalar cone is preserved by coefficient restriction. -/
@[reassoc] lemma restrictionScalarConeIso_inr
    (a : R) (b : S) (hab : φ a = b) (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr (smulId b K)) ≫
      (restrictionScalarConeIso φ a b hab K).hom =
      CochainComplex.mappingCone.inr (smulId a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K)) := by
  apply (cancel_mono (restrictionScalarConeIso φ a b hab K).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext i
  exact (restrictionScalarConeIso_inv_inr φ a b hab K i).symm

/-- The actual descending power-Koszul transitions commute with the inverse comparisons. -/
@[reassoc] lemma restrictionPowerKoszulStageIso_inv_transition
    (a : R) (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    (restrictionPowerKoszulStageIso φ a K (n + 1)).inv ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
          (complexPowerKoszulTransition S (φ a) K n) =
      complexPowerKoszulTransition R a
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n ≫
        (restrictionPowerKoszulStageIso φ a K n).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ext_from_X
    (smulId (a ^ (n + 1))
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K))
    (i + 1) i rfl
  · simp only [restrictionPowerKoszulStageIso, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, complexPowerKoszulTransition]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inl,
      ← CategoryTheory.Functor.map_comp, moduleConeArrowMap_inl,
      CategoryTheory.Functor.map_comp, moduleConeArrowMap_inl_assoc,
      restrictionScalarConeIso_inv_inl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · simp only [restrictionPowerKoszulStageIso, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, complexPowerKoszulTransition]
    rw [← Category.assoc, restrictionScalarConeIso_inv_inr,
      ← CategoryTheory.Functor.map_comp, moduleConeArrowMap_inr,
      CategoryTheory.Functor.map_comp, moduleConeArrowMap_inr_assoc,
      restrictionScalarConeIso_inv_inr]
    rfl

/-- The forward comparisons intertwine exactly the original power-Koszul transition maps. -/
@[reassoc] lemma restrictionPowerKoszulStageIso_transition
    (a : R) (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (complexPowerKoszulTransition S (φ a) K n) ≫
      (restrictionPowerKoszulStageIso φ a K n).hom =
      (restrictionPowerKoszulStageIso φ a K (n + 1)).hom ≫
        complexPowerKoszulTransition R a
          (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) n := by
  have h := congrArg (fun f ↦ (restrictionPowerKoszulStageIso φ a K (n + 1)).hom ≫ f ≫
    (restrictionPowerKoszulStageIso φ a K n).hom)
    (restrictionPowerKoszulStageIso_inv_transition φ a K n)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

end SerrePositivity.DerivedCompletion
