module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteIdealExtension
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraMilnorSequence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraComplete
public import SerrePositivity.HomologicalAlgebra.TorFiniteCoefficients

/-! # Full Tor annihilation from power-torsion tests and complete almost extension closure

The extension-closure property is an explicit mathematical input, corresponding
to the part of BS10.2 used here. It is not inferred from ordinary mod-pⁿ ideal
idempotence, and no assertion of its perfectoid application is made in this file.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory


variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  (p : ℕ) (C : Type u) [CommRing C] [Algebra R C]
  (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
  (hC : IsModuleComplete R (p : R) (ModuleCat.of R C))
  (hExt : CompleteIdealExtensionClosed B (p : B) I)
  (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
    (∀ x : N, (p : R) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
      ∀ b ∈ I, torCoefficientScalarEndomorphism C N j (ψ b) = 0)

include hC hExt hTor in
/-- The actual coefficient-linear Milnor sequence supplies almost zero for finite tests. -/
lemma finite_tor_eq_zero_of_power_torsion_and_complete_extensions
    (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) (hi : 0 < i)
    (b : B) (hb : b ∈ I) : torCoefficientScalarEndomorphism C M i (ψ b) = 0 := by
  let S := torAlgebraMilnorShortComplexOver (p : R) C M hC i B ψ
  have hs : S.ShortExact := torAlgebraMilnorShortComplexOver_shortExact (p : R) C M hC i B ψ
  have h₁ : IsModuleComplete B (p : B) S.X₁ :=
    modulePowerTorAlgebraLimOne_isModuleComplete_restrict C M (i + 1) B ψ p
  have h₂ : IsModuleComplete B (p : B) S.X₂ :=
    torAlgebra_isModuleComplete_restrict_of_finite C M B ψ p hC i
  have h₃ : IsModuleComplete B (p : B) S.X₃ :=
    modulePowerTorAlgebraLimit_isModuleComplete_restrict C M i B ψ p
  have ha₁ : I ≤ Module.annihilator B S.X₁ :=
    modulePowerTorAlgebraLimOne_annihilated (p : R) C M (i + 1) B ψ I
      (fun N k hk hN => hTor N k hk hN (i + 1) (Nat.succ_pos _))
  have ha₃ : I ≤ Module.annihilator B S.X₃ :=
    modulePowerTorAlgebraLimit_annihilated (p : R) C M i B ψ I
      (fun N k hk hN => hTor N k hk hN i hi)
  have ha := hExt S hs h₁ h₂ h₃ ha₁ ha₃
  exact (torAlgebraComparison_restricted_annihilator_iff B ψ I M i).mpr ha b hb

include hC hExt hTor in
/-- The full original test quantifiers: arbitrary modules, all positive Tor and every ideal element. -/
lemma tor_eq_zero_of_power_torsion_and_complete_extensions
    (M : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C M i (ψ b) = 0 := by
  apply torCoefficientScalarEndomorphism_eq_zero_of_finite C i (ψ b) _ M
  intro N hN
  letI := hN
  exact finite_tor_eq_zero_of_power_torsion_and_complete_extensions p C B ψ I hC hExt hTor N i hi b hb

end SerrePositivity.DerivedCompletion
