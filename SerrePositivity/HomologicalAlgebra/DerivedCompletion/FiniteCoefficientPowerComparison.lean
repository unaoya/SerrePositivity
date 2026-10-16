module

public import SerrePositivity.CommutativeAlgebra.ModulePowerTorsionBound
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedTermTorsionComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteTensorComplete
public import SerrePositivity.HomologicalAlgebra.DerivedTensorUnresolvedModule
public import SerrePositivity.HomologicalAlgebra.DerivedTensorSymmetry

/-! # Standard power-quotient comparison in the finite-coefficient tensor model

Resolve the complete coefficient module C and leave the finite test module M
unresolved. M's own torsion bound passes to every projective term of that model.
Neither M nor its tensor with C is assumed flat.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (a : R)
    (C M : ModuleCat.{u} R) [Module.Finite R M]

/-- The actual projective-resolution model with the finite test module unresolved. -/
abbrev finiteCoefficientTensorModel : CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleTensorCochainFunctor (extRes (projectiveResolution C))).obj M

/-- The finite test module's bound is uniform over every term of the original
coefficient resolution, even if that resolution has infinite length. -/
lemma finiteCoefficientTensorModel_has_torsion_bound :
    ∃ N : ℕ, ∀ (i : ℤ) (n : ℕ) (x : (finiteCoefficientTensorModel R C M).X i),
      a ^ n • x = 0 → a ^ N • x = 0 := by
  obtain ⟨N, hN⟩ := exists_power_torsion_bound_of_finite (M := M) a
  refine ⟨N, fun i => ?_⟩
  have : Module.Projective R ((extRes (projectiveResolution C)).X i) := inferInstance
  have : Module.Flat R ((extRes (projectiveResolution C)).X i) := inferInstance
  exact flat_tensor_power_torsion_bound a N hN

/-- The same model represents the complete actual tensor; factor exchange is
the existing signed derived symmetry. -/
lemma finiteCoefficientTensorModel_isComplete (hC : IsModuleComplete R a C) :
    IsComplete R a (DerivedCategory.Q.obj (finiteCoefficientTensorModel R C M)) := by
  let e := (DerivedCategory.Minus.ι (C := ModuleCat.{u} R)).mapIso
    (boundedAboveDerivedTensorSymmetry (boundedAboveDerivedSingleFunctor.obj C)
      (boundedAboveDerivedSingleFunctor.obj M))
  have hc := isComplete_of_iso R a e
    (boundedAboveDerivedTensor_isComplete_of_finite_regular R a C M hC)
  exact isComplete_of_iso R a
    (derivedTensorUnresolvedModuleModelIso M (boundedAboveDerivedSingleFunctor.obj C)
      (projectiveResolutionDerivedModel (projectiveResolution C))) hc

/-- The standard Koszul-to-ordinary-power-cokernel comparison is a genuine
quasi-isomorphism in the model of C ⊗ᴸ M. -/
lemma finiteCoefficientPowerComparison_quasiIso (hC : IsModuleComplete R a C) :
    QuasiIso (koszulPowerCokernelComparison a (finiteCoefficientTensorModel R C M)) := by
  obtain ⟨N, hN⟩ := finiteCoefficientTensorModel_has_torsion_bound R a C M
  exact koszulPowerCokernelComparison_quasiIso_of_term_bound a _ N hN
    (finiteCoefficientTensorModel_isComplete R a C M hC)

end SerrePositivity.DerivedCompletion
