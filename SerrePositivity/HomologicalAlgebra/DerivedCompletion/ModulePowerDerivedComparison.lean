module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTensorModel
public import SerrePositivity.HomologicalAlgebra.DerivedTensorFixedModuleModel

/-! # Actual C ⊗ᴸ M/aⁿM, with the original quotient and transition maps -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (C M : ModuleCat.{u} R)

lemma moduleCoefficientResolution_flat (i : ℤ) :
    Module.Flat R ((extRes (projectiveResolution C)).X i) := by
  have : Module.Projective R ((extRes (projectiveResolution C)).X i) := inferInstance
  infer_instance

/-- Each original power cokernel computes the actual tensor of C with the
ordinary quotient M/aⁿM. No regularity or completeness assumptions are needed. -/
def modulePowerDerivedTensorIso (n : ℕ) :
    DerivedCategory.Q.obj (powerCokernelComplex a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) ≅
        (boundedAboveDerivedTensorModuleFunctor C).obj (modulePowerReduction a M n) :=
  DerivedCategory.Q.mapIso (modulePowerTensorModelIso a M
    (extRes (projectiveResolution C)) (moduleCoefficientResolution_flat C) n) ≪≫
      (derivedTensorCoefficientModelIso C (modulePowerReduction a M n)).symm

/-- The actual derived reduction map is the original quotient map under the
comparison, not a map selected after identifying the two objects. -/
@[reassoc] lemma modulePowerDerivedTensorIso_π (n : ℕ) :
    DerivedCategory.Q.map (cokernel.π (smulId (a ^ n)
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M))) ≫
        (modulePowerDerivedTensorIso a C M n).hom =
      (derivedTensorCoefficientModelIso C M).inv ≫
        (boundedAboveDerivedTensorModuleFunctor C).map (modulePowerReductionMap a M n) := by
  let f := modulePowerReductionMap a M n
  let eM := derivedTensorCoefficientModelIso C M
  let eN := derivedTensorCoefficientModelIso C (modulePowerReduction a M n)
  let pf := DerivedCategory.Q.map
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).map f)
  have h : pf ≫ eN.inv = eM.inv ≫ (boundedAboveDerivedTensorModuleFunctor C).map f := by
    apply (cancel_epi eM.hom).mp
    rw [← Category.assoc, ← derivedTensorCoefficientModelIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  simp only [modulePowerDerivedTensorIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, ← Category.assoc, ← Functor.map_comp, modulePowerTensorModelIso_π]
  exact h

/-- The original power-cokernel transition becomes the actual derived map
induced by M/aⁿ⁺¹M → M/aⁿM. -/
@[reassoc] lemma modulePowerDerivedTensorIso_transition (n : ℕ) :
    DerivedCategory.Q.map (powerCokernelComplexTransition a
      ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M) n) ≫
        (modulePowerDerivedTensorIso a C M n).hom =
      (modulePowerDerivedTensorIso a C M (n + 1)).hom ≫
        (boundedAboveDerivedTensorModuleFunctor C).map (modulePowerReductionTransition a M n) := by
  let f := modulePowerReductionTransition a M n
  let eM := derivedTensorCoefficientModelIso C (modulePowerReduction a M (n + 1))
  let eN := derivedTensorCoefficientModelIso C (modulePowerReduction a M n)
  let pf := DerivedCategory.Q.map
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).map f)
  have h : pf ≫ eN.inv = eM.inv ≫ (boundedAboveDerivedTensorModuleFunctor C).map f := by
    apply (cancel_epi eM.hom).mp
    rw [← Category.assoc, ← derivedTensorCoefficientModelIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht := congrArg DerivedCategory.Q.map
    (modulePowerTensorModelIso_transition a M (extRes (projectiveResolution C))
      (moduleCoefficientResolution_flat C) n)
  simp only [Functor.map_comp] at ht
  simp only [modulePowerDerivedTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ht, Category.assoc]
  change _ ≫ (pf ≫ eN.inv) = (_ ≫ eM.inv) ≫ _
  rw [h, Category.assoc]

variable {C} {D : ModuleCat.{u} R}

/-- The derived comparison keeps every coefficient map, using its original
resolution lift; multiplication maps give the Tor actions used by KL. -/
@[reassoc] lemma modulePowerDerivedTensorIso_naturality
    (f : C ⟶ D) (n : ℕ) :
    DerivedCategory.Q.map (modulePowerTensorCokernelMap a M
      (extLift (projectiveResolution C) f (projectiveResolution D)) n) ≫
        (modulePowerDerivedTensorIso a D M n).hom =
      (modulePowerDerivedTensorIso a C M n).hom ≫
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
          (boundedAboveDerivedSingleFunctor.map f)
          (𝟙 (boundedAboveDerivedSingleFunctor.obj (modulePowerReduction a M n))))).hom := by
  let N := modulePowerReduction a M n
  let eC := derivedTensorCoefficientModelIso C N
  let eD := derivedTensorCoefficientModelIso D N
  let pf := DerivedCategory.Q.map
    (((MonoidalCategory.tensorLeft N).mapHomologicalComplex (.up ℤ)).map
      (extLift (projectiveResolution C) f (projectiveResolution D)))
  let df := (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
    (boundedAboveDerivedSingleFunctor.map f) (𝟙 (boundedAboveDerivedSingleFunctor.obj N)))).hom
  have h : pf ≫ eD.inv = eC.inv ≫ df := by
    apply (cancel_epi eC.hom).mp
    rw [← Category.assoc, ← derivedTensorCoefficientModelIso_naturality_left,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have ht := congrArg DerivedCategory.Q.map
    (modulePowerTensorModelIso_naturality a M
      (extLift (projectiveResolution C) f (projectiveResolution D))
      (moduleCoefficientResolution_flat C) (moduleCoefficientResolution_flat D) n)
  simp only [Functor.map_comp] at ht
  simp only [modulePowerDerivedTensorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, ht, Category.assoc]
  change _ ≫ (pf ≫ eD.inv) = (_ ≫ eC.inv) ≫ df
  rw [h, Category.assoc]

end SerrePositivity.DerivedCompletion
