module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTensorHolim
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientPowerComparison

/-! # The original finite-coefficient derived tensor is reconstructed from M/aⁿM

All stages and transitions are the original ones, with the actual derived stage
comparison and a standard projection formula. No vanishing of lim¹ is assumed.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (C M : ModuleCat.{u} R)

/-- A concrete model for the holim of the actual C ⊗ᴸ (M/aⁿM) stages. -/
abbrev modulePowerDerivedTensorHolimComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  complexTowerHomotopyLimit R (modulePowerTensorTower a M (extRes (projectiveResolution C)))
    (modulePowerTensorTransition a M (extRes (projectiveResolution C)))

/-- The original holim projection followed by the actual derived stage comparison. -/
def modulePowerDerivedTensorHolimProjection (n : ℕ) :
    DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a C M) ⟶
      (boundedAboveDerivedTensorModuleFunctor C).obj (modulePowerReduction a M n) :=
  DerivedCategory.Q.map (complexTowerProjection R
    (modulePowerTensorTower a M (extRes (projectiveResolution C)))
    (modulePowerTensorTransition a M (extRes (projectiveResolution C))) ≫
      Pi.π (modulePowerTensorTower a M (extRes (projectiveResolution C))) n) ≫
        (derivedTensorCoefficientModelIso C (modulePowerReduction a M n)).inv

variable [IsRegularLocalRing R] [Module.Finite R M]

/-- Completeness of C and finiteness of M supply both actual reconstruction inputs. -/
lemma finiteCoefficientPowerReconstruction_quasiIso (hC : IsModuleComplete R a C) :
    QuasiIso (modulePowerTensorReconstruction a M (extRes (projectiveResolution C))) := by
  obtain ⟨N, hN⟩ := finiteCoefficientTensorModel_has_torsion_bound R a C M
  exact modulePowerTensorReconstruction_quasiIso a M (extRes (projectiveResolution C))
    (moduleCoefficientResolution_flat C) N hN
    (finiteCoefficientTensorModel_isComplete R a C M hC)

/-- The same actual C ⊗ᴸ M is the holim of its ordinary test-module quotient stages. -/
def finiteCoefficientPowerHolimIso (hC : IsModuleComplete R a C) :
    (boundedAboveDerivedTensorModuleFunctor C).obj M ≅
      DerivedCategory.Q.obj (modulePowerDerivedTensorHolimComplex R a C M) := by
  have := finiteCoefficientPowerReconstruction_quasiIso R a C M hC
  exact derivedTensorCoefficientModelIso C M ≪≫
    asIso (DerivedCategory.Q.map
      (modulePowerTensorReconstruction a M (extRes (projectiveResolution C))))

/-- Every projection is precisely the original derived quotient map. -/
@[reassoc] lemma finiteCoefficientPowerHolimIso_projection
    (hC : IsModuleComplete R a C) (n : ℕ) :
    (finiteCoefficientPowerHolimIso R a C M hC).hom ≫
      modulePowerDerivedTensorHolimProjection R a C M n =
        (boundedAboveDerivedTensorModuleFunctor C).map (modulePowerReductionMap a M n) := by
  have h := derivedTensorCoefficientModelIso_naturality C (modulePowerReductionMap a M n)
  simp only [finiteCoefficientPowerHolimIso, Iso.trans_hom, asIso_hom,
    modulePowerDerivedTensorHolimProjection, Category.assoc]
  rw [← Category.assoc (DerivedCategory.Q.map _), ← Functor.map_comp,
    modulePowerTensorReconstruction_projection]
  change _ ≫ (DerivedCategory.Q.map
    ((moduleTensorCochainFunctor (extRes (projectiveResolution C))).map
      (modulePowerReductionMap a M n)) ≫ _) = _
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.DerivedCompletion
