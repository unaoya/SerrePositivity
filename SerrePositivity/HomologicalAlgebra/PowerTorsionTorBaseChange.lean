module

public import SerrePositivity.HomologicalAlgebra.TorAlgebraAcyclicBaseChange
public import SerrePositivity.HomologicalAlgebra.ModuleScalarExtensionAnnihilator

/-! # Transport power-torsion almost Tor tests along a flat change of base

Tests over R are extended using the original functor R→B. The actual coefficient
algebra C and the original B-ideal action are retained. No completeness is assumed.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory
variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Module.Flat R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]

/-- The B-power-torsion Tor input supplies all original R-power-torsion tests,
with the same positive exponent, degree, and ideal element. -/
lemma powerTorsionTorInput_of_flat_baseChange (p : ℕ) (I : Ideal B)
    (hTor : ∀ (L : ModuleCat.{u} B) (k : ℕ), 0 < k →
      (∀ x : L, (p : B) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
        ∀ b ∈ I, torCoefficientScalarEndomorphism C L j (algebraMap B C b) = 0)
    (N : ModuleCat.{u} R) (k : ℕ) (hk : 0 < k)
    (hN : ∀ x : N, (p : R) ^ k • x = 0)
    (j : ℕ) (hj : 0 < j) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C N j (algebraMap B C b) = 0 := by
  let L := (ModuleCat.extendScalars (algebraMap R B)).obj N
  have hL : ∀ x : L, (p : B) ^ k • x = 0 := by
    have hs := scalarExtension_annihilated (algebraMap R B) ((p : R) ^ k) N hN
    simpa only [map_pow, map_natCast] using hs
  exact (torCoefficientScalarEndomorphism_acyclicBaseChange_eq_zero_iff N
    (scalarExtensionTorVanishing_of_flat_algebra N) j (algebraMap B C b)).mpr
      (hTor L k hk hL j hj b hb)

end SerrePositivity
