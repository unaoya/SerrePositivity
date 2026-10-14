module
public import SerrePositivity.KTheory.DevissageAnnihilated

/-! # Finite filtrations with factors annihilated by an ideal -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits
open scoped Pointwise
variable {R : Type u} [CommRing R]

/-- A finite descending filtration, specified by its successive submodule and quotient. -/
inductive DevissageFlag (J : Ideal R) : ModuleCat.{u} R → Type (u + 1)
  | zero {M : ModuleCat.{u} R} (h : IsZero M) : DevissageFlag J M
  | step {M : ModuleCat.{u} R} (U : Submodule R M) (h : J ≤ Module.annihilator R (M ⧸ U))
      (rest : DevissageFlag J (ModuleCat.of R U)) : DevissageFlag J M

/-- Support in V(J) supplies an annihilating power for a finite module. -/
lemma exists_pow_annihilator_of_support [IsNoetherianRing R]
    (J : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hs : Module.support R M ⊆ supportZeroLocus J) :
    ∃ n : ℕ, J ^ n ≤ Module.annihilator R M := by
  change Module.support R M ⊆ PrimeSpectrum.zeroLocus J at hs
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hs
  exact Ideal.exists_pow_le_of_le_radical_of_fg hs J.fg_of_isNoetherianRing

/-- Passing to JM removes one power from an annihilator bound. -/
lemma pow_annihilator_ideal_smul (J : Ideal R) (M : ModuleCat.{u} R) (n : ℕ)
    (h : J ^ (n + 1) ≤ Module.annihilator R M) :
    J ^ n ≤ Module.annihilator R ((J • ⊤ : Submodule R M)) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  change r • (x : M) = 0
  refine Submodule.smul_induction_on x.property (fun s hs y hy => ?_)
    (fun x y hx hy => ?_)
  · rw [← mul_smul]
    exact Module.mem_annihilator.mp (h (by
      rw [pow_succ]
      exact Ideal.mul_mem_mul hr hs)) y
  · rw [smul_add, hx, hy, add_zero]

/-- The first quotient of the ideal-power filtration is annihilated by J. -/
lemma ideal_smul_quotient_annihilator (J : Ideal R) (M : ModuleCat.{u} R) :
    J ≤ Module.annihilator R (M ⧸ (J • ⊤ : Submodule R M)) := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  exact (Module.isTorsionBySet_quotient_ideal_smul M J) (x := x) (a := ⟨r, hr⟩)

/-- An annihilating power produces a finite filtration, without any regularity assumption. -/
lemma exists_devissageFlag_of_pow (J : Ideal R) (n : ℕ) :
    ∀ (M : ModuleCat.{u} R), J ^ n ≤ Module.annihilator R M → Nonempty (DevissageFlag J M) := by
  induction n with
  | zero =>
    intro M h
    have h1 : (1 : R) ∈ Module.annihilator R M := h (by simp)
    have hz : ∀ x : M, x = 0 := fun x => by
      simpa using Module.mem_annihilator.mp h1 x
    have : Subsingleton M := ⟨fun x y => (hz x).trans (hz y).symm⟩
    exact ⟨.zero (ModuleCat.isZero_of_subsingleton M)⟩
  | succ n ih =>
    intro M h
    obtain ⟨F⟩ := ih (ModuleCat.of R ((J • ⊤ : Submodule R M)))
      (pow_annihilator_ideal_smul J M n h)
    exact ⟨.step _ (ideal_smul_quotient_annihilator J M) F⟩

/-- Every finite module supported in V(J) has an annihilated-factor filtration. -/
lemma exists_devissageFlag [IsNoetherianRing R] (J : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hs : Module.support R M ⊆ supportZeroLocus J) : Nonempty (DevissageFlag J M) := by
  obtain ⟨n, hn⟩ := exists_pow_annihilator_of_support J M hs
  exact exists_devissageFlag_of_pow J n M hn

/-- Sum the quotient-ring classes of the factors of a filtration. -/
def DevissageFlag.value [IsNoetherianRing R] {J : Ideal R} {M : ModuleCat.{u} R}
    (F : DevissageFlag J M) [Module.Finite R M] : G0 (R ⧸ J) :=
  match F with
  | .zero _ => 0
  | .step U h rest => rest.value + annihilatedClass J (ModuleCat.of R (M ⧸ U)) h

end SerrePositivity
