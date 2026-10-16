module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction

/-! # Derived completeness of an integral perfectoid algebra

Use the classical completeness in the definition and preserve it on restriction
to any coefficient ring. Neither torsion-freeness nor bounded torsion is needed.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open DerivedCompletion

/-- An integral perfectoid ring, including the zero ring, is derived p-complete. -/
lemma IsIntegralPerfectoid.isModuleComplete
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    (hS : IsIntegralPerfectoid S p) :
    IsModuleComplete S (p : S) (ModuleCat.of S S) := by
  rcases hS with hS | ⟨_, hc, _⟩
  · let : Subsingleton S := hS
    exact isModuleComplete_of_pow_smul_zero S (p : S) _ 0
      (fun _ => Subsingleton.elim _ _)
  · let := hc
    exact isModuleComplete_of_isAdicComplete S (p : S) (ModuleCat.of S S)

/-- The original algebra action of any base ring gives a derived p-complete
coefficient module. -/
lemma IsIntegralPerfectoid.isModuleComplete_algebra
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsModuleComplete R (p : R) (ModuleCat.of R S) := by
  apply (isModuleComplete_algebraMap_iff R S (p : R) S).mp
  simpa only [map_natCast] using hS.isModuleComplete S p

end SerrePositivity
