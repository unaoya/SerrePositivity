module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteCoefficientPowerComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerDerivedComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelNaturality

/-! # The original tensor comparison with the power-cokernel Milnor middle -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
    (C M : ModuleCat.{u} R) [Module.Finite R M]

/-- The original power-cokernel reconstruction is a quasi-isomorphism for finite tests. -/
lemma finiteCoefficientPowerCokernelReconstruction_quasiIso (hC : IsModuleComplete R a C) :
    QuasiIso (powerCokernelReconstruction a (finiteCoefficientTensorModel R C M)) := by
  obtain ⟨N, hN⟩ := finiteCoefficientTensorModel_has_torsion_bound R a C M
  exact powerCokernelReconstruction_quasiIso_of_term_bound a _ N hN
    (finiteCoefficientTensorModel_isComplete R a C M hC)

/-- Use the existing actual tensor and the original reconstruction, with no new completion choice. -/
def finiteCoefficientPowerCokernelHolimIso (hC : IsModuleComplete R a C) :
    (boundedAboveDerivedTensorModuleFunctor C).obj M ≅
      DerivedCategory.Q.obj (complexTowerHomotopyLimit R
        (powerCokernelComplex a (finiteCoefficientTensorModel R C M))
        (powerCokernelComplexTransition a (finiteCoefficientTensorModel R C M))) := by
  have := finiteCoefficientPowerCokernelReconstruction_quasiIso a C M hC
  exact derivedTensorCoefficientModelIso C M ≪≫
    asIso (DerivedCategory.Q.map (powerCokernelReconstruction a (finiteCoefficientTensorModel R C M)))

/-- Naturality uses the original lift of the coefficient morphism. -/
@[reassoc] lemma finiteCoefficientPowerCokernelHolimIso_naturality_left
    {D : ModuleCat.{u} R} (f : C ⟶ D)
    (hC : IsModuleComplete R a C) (hD : IsModuleComplete R a D) :
    (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
      (boundedAboveDerivedSingleFunctor.map f)
      (𝟙 (boundedAboveDerivedSingleFunctor.obj M)))).hom ≫
        (finiteCoefficientPowerCokernelHolimIso a D M hD).hom =
      (finiteCoefficientPowerCokernelHolimIso a C M hC).hom ≫
        DerivedCategory.Q.map (powerCokernelHolimMap a
          (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
            (extLift (projectiveResolution C) f (projectiveResolution D)))) := by
  have hn := derivedTensorCoefficientModelIso_naturality_left M f
  have hr := powerCokernelReconstruction_naturality a
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
      (extLift (projectiveResolution C) f (projectiveResolution D)))
  change powerCokernelReconstruction a (finiteCoefficientTensorModel R C M) ≫
      powerCokernelHolimMap a (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
        (extLift (projectiveResolution C) f (projectiveResolution D))) =
    (((tensorLeft M).mapHomologicalComplex (.up ℤ)).map
      (extLift (projectiveResolution C) f (projectiveResolution D))) ≫
        powerCokernelReconstruction a (finiteCoefficientTensorModel R D M) at hr
  simp only [finiteCoefficientPowerCokernelHolimIso, Iso.trans_hom, asIso_hom]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    ← hr, Functor.map_comp, ← Category.assoc]

end SerrePositivity.DerivedCompletion
