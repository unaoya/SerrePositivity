module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorOneCompleteExtension
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerTorsionTorExtension

/-! # Full Tor annihilation with a concrete conormal or quotient-Tor₁ input -/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  (p : ℕ) (C : Type u) [CommRing C] [Algebra R C]
  (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
  (hC : IsModuleComplete R (p : R) (ModuleCat.of R C))
  (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
    (∀ x : N, (p : R) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
      ∀ b ∈ I, torCoefficientScalarEndomorphism C N j (ψ b) = 0)

include hC hTor in
lemma tor_eq_zero_of_power_torsion_and_quotientTorOne
    (hQ : Function.Surjective
      (fun x : TorModule B 1 (B ⧸ I) (B ⧸ I) => (p : B) • x))
    (M : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C M i (ψ b) = 0 :=
  tor_eq_zero_of_power_torsion_and_complete_extensions p C B ψ I hC
    (completeIdealExtensionClosed_of_quotientTorOne_surjective (p : B) I hQ) hTor M i hi b hb

include hC hTor in
lemma tor_eq_zero_of_power_torsion_and_conormal
    (hI : Function.Surjective (fun x : I.Cotangent => (p : B) • x))
    (M : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C M i (ψ b) = 0 :=
  tor_eq_zero_of_power_torsion_and_complete_extensions p C B ψ I hC
    (completeIdealExtensionClosed_of_conormal_surjective (p : B) I hI) hTor M i hi b hb

end SerrePositivity.DerivedCompletion
