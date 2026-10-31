module

public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealCompatibleRoots
public import SerrePositivity.HomologicalAlgebra.Koszul.ParameterAnnihilators

/-! # Compatible roots detect the original full perfectoid-ideal Tor input

All test modules and the original coefficient endomorphisms are retained. There
is no finite generation, completeness, flatness, or regularity assumption on them.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (ρ : ℕ → R)
    (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (C : Type u) [CommRing C] [Algebra R C]
include hρ

/-- Original coefficient zero actions on Tor are detected by the given compatible roots. -/
theorem perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
    (N : ModuleCat.{u} R) (k : ℕ) (hN : ∀ x : N, (p : R) ^ k • x = 0) (i : ℕ) :
    (∀ s ∈ perfectoidIdeal R p hR (ρ 0),
      torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
      ∀ n, torCoefficientScalarEndomorphism C N i (algebraMap R C (ρ n)) = 0 := by
  let F := (Tor (ModuleCat.{u} R) i).flip.obj N
  let J := (coefficientFunctorAnnihilator (C := C) F).comap (algebraMap R C)
  have hp : (p : R) ^ k ∈ J :=
    torCoefficientScalar_algebraMap_eq_zero_of_annihilates N i ((p : R) ^ k) hN
  change (perfectoidIdeal R p hR (ρ 0) ≤ J) ↔ ∀ n, ρ n ∈ J
  exact perfectoidIdeal_le_iff_compatible_roots R p hR ρ hρ J k hp

/-- The full power-torsion Tor input is equivalent to tests on every compatible root. -/
theorem perfectoidIdeal_powerTorsionTorInput_iff_compatible_roots :
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ s ∈ perfectoidIdeal R p hR (ρ 0),
        torCoefficientScalarEndomorphism C N i (algebraMap R C s) = 0) ↔
    (∀ (N : ModuleCat.{u} R) (k : ℕ), (∀ x : N, (p : R) ^ k • x = 0) →
      ∀ i : ℕ, 0 < i → ∀ n,
        torCoefficientScalarEndomorphism C N i (algebraMap R C (ρ n)) = 0) := by
  constructor
  · intro h N k hN i hi
    exact (perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
      R p hR ρ hρ C N k hN i).mp (h N k hN i hi)
  · intro h N k hN i hi
    exact (perfectoidIdeal_torCoefficientScalar_eq_zero_iff_compatible_roots
      R p hR ρ hρ C N k hN i).mpr (h N k hN i hi)

end SerrePositivity.CLMST
