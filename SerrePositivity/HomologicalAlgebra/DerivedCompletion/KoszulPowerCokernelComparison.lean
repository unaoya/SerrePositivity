module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelReconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction

/-! # The actual augmentation from the Koszul tower to the ordinary power quotient tower -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev powerScalarCokernelShortComplex (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (smulId (a ^ n) K) (cokernel.π (smulId (a ^ n) K)) (cokernel.condition _)

/-- The actual standard augmentation; it need not be a quasi-isomorphism at a stage. -/
def koszulPowerCokernelAugmentation (n : ℕ) :
    complexPowerKoszulStage R a K n ⟶ powerCokernelComplex a K n :=
  CochainComplex.mappingCone.descShortComplex (powerScalarCokernelShortComplex a K n)

@[reassoc] lemma koszulPowerCokernelAugmentation_inr (n : ℕ) :
    CochainComplex.mappingCone.inr (smulId (a ^ n) K) ≫
      koszulPowerCokernelAugmentation a K n = cokernel.π (smulId (a ^ n) K) := by
  apply CochainComplex.mappingCone.inr_descShortComplex

lemma koszulPowerCokernelAugmentation_transition (n : ℕ) :
    complexPowerKoszulTransition R a K n ≫ koszulPowerCokernelAugmentation a K n =
      koszulPowerCokernelAugmentation a K (n + 1) ≫ powerCokernelComplexTransition a K n := by
  let f : powerScalarCokernelShortComplex a K (n + 1) ⟶ powerScalarCokernelShortComplex a K n :=
    { τ₁ := smulId a K
      τ₂ := 𝟙 K
      τ₃ := powerCokernelComplexTransition a K n
      comm₁₂ := powerScalar_square a K n
      comm₂₃ := by simpa using (powerCokernelComplexTransition_π a K n).symm }
  have hm : complexPowerKoszulTransition R a K n =
      CochainComplex.mappingCone.map (smulId (a ^ (n + 1)) K) (smulId (a ^ n) K)
        (a • 𝟙 K) (𝟙 K) (powerScalar_square a K n).symm :=
    cochainMappingConeFunctor_map_eq R
      (X := Arrow.mk (smulId (a ^ (n + 1)) K)) (Y := Arrow.mk (smulId (a ^ n) K))
      (Arrow.homMk (a • 𝟙 K) (𝟙 K) (powerScalar_square a K n))
  rw [hm]
  have hn := CochainComplex.mappingCone.map_descShortComplex
    (powerScalarCokernelShortComplex a K (n + 1)) (powerScalarCokernelShortComplex a K n) f
  exact hn

/-- The standard augmentation of towers induces this actual chain map on holims. -/
def koszulPowerCokernelComparison :
    (complexCompletionFunctor R a).obj K ⟶
      complexTowerHomotopyLimit R (powerCokernelComplex a K) (powerCokernelComplexTransition a K) :=
  complexTowerHomotopyLimitMap R (complexPowerKoszulTransition R a K)
    (powerCokernelComplexTransition a K) (koszulPowerCokernelAugmentation a K)
    (koszulPowerCokernelAugmentation_transition a K)

@[reassoc] lemma complexCompletionUnit_comp_koszulPowerCokernelComparison :
    complexCompletionUnit R a K ≫ koszulPowerCokernelComparison a K =
      powerCokernelReconstruction a K := by
  rw [powerCokernelReconstruction_eq_lift]
  apply complexTowerCompatibleLift_map
  exact koszulPowerCokernelAugmentation_inr a K

/-- Bounded coefficient torsion makes the actual tower augmentation a quasi-isomorphism
on a complete flat complex; regularity of a is not required. -/
theorem koszulPowerCokernelComparison_quasiIso (hK : ∀ i, Module.Flat R (K.X i))
    (N : ℕ) (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj K)) :
    QuasiIso (koszulPowerCokernelComparison a K) := by
  have := complexCompletionUnit_quasiIso_of_isComplete R a K hc
  have : QuasiIso (complexCompletionUnit R a K ≫ koszulPowerCokernelComparison a K) := by
    rw [complexCompletionUnit_comp_koszulPowerCokernelComparison]
    exact powerCokernelReconstruction_quasiIso a K hK N h hc
  exact (quasiIso_iff_comp_left (complexCompletionUnit R a K) _).mp inferInstance

end SerrePositivity.DerivedCompletion
