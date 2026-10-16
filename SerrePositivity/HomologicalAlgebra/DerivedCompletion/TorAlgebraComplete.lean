module

public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FiniteTensorComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionHomologyComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction

/-! # Actual finite-test Tor modules are derived complete over their coefficient algebra -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C]
  (M : ModuleCat.{u} R) [Module.Finite R M]

/-- Completeness of the actual tensor supplies completeness of the existing standard Tor. -/
lemma torModule_isModuleComplete_of_finite (hC : IsModuleComplete R a (ModuleCat.of R C))
    (i : ℕ) : IsModuleComplete R a
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R C)).obj M) := by
  have hc := boundedAboveDerivedTensor_isComplete_of_finite_regular R a (ModuleCat.of R C) M hC
  have hh := isComplete_homology_isModuleComplete R a _ hc (-(i : ℤ))
  exact isModuleComplete_of_linearEquiv R a _ _
    ((boundedAboveDerivedTensorModuleTorNatIso (ModuleCat.of R C) i).app M).toLinearEquiv hh

/-- The algebra-valued Tor is complete after restriction along the original base action. -/
lemma restrictedTorAlgebra_isModuleComplete_of_finite
    (hC : IsModuleComplete R a (ModuleCat.of R C)) (i : ℕ) :
    IsModuleComplete R a ((ModuleCat.restrictScalars (algebraMap R C)).obj
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) :=
  isModuleComplete_of_linearEquiv R a _ _ (torAlgebraComparison (C := C) M i).toLinearEquiv
    (torModule_isModuleComplete_of_finite a C M hC i)

/-- In its actual C-module structure, finite-test Tor is derived complete for the image of a. -/
lemma torAlgebra_isModuleComplete_of_finite
    (hC : IsModuleComplete R a (ModuleCat.of R C)) (i : ℕ) :
    IsModuleComplete C (algebraMap R C a)
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M) := by
  let X := ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M
  letI : Module R X := Module.compHom X (algebraMap R C)
  letI : IsScalarTower R C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  exact (isModuleComplete_algebraMap_iff R C a X).mpr
    (restrictedTorAlgebra_isModuleComplete_of_finite a C M hC i)

/-- For a natural-number parameter, completeness also holds over any original
coefficient source B→C; no finiteness hypothesis on B or C is imposed. -/
lemma torAlgebra_isModuleComplete_restrict_of_finite
    (B : Type u) [CommRing B] (ψ : B →+* C) (p : ℕ)
    (hC : IsModuleComplete R (p : R) (ModuleCat.of R C)) (i : ℕ) :
    IsModuleComplete B (p : B) ((ModuleCat.restrictScalars ψ).obj
      (((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M)) := by
  letI : Algebra B C := ψ.toAlgebra
  let X := ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M
  letI : Module B X := Module.compHom X ψ
  letI : IsScalarTower B C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  have hc : IsModuleComplete C (algebraMap B C (p : B)) X := by
    simpa only [map_natCast] using torAlgebra_isModuleComplete_of_finite (p : R) C M hC i
  exact (isModuleComplete_algebraMap_iff B C (p : B) X).mp hc

end SerrePositivity.DerivedCompletion
