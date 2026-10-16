module

public import SerrePositivity.CommutativeAlgebra.FlatPowerTorsion
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Uniform control of torsion in flat modules over power quotients -/

@[expose] public noncomputable section
namespace SerrePositivity
variable {R : Type*} [CommRing R] (a : R) (N : ℕ)
    (h : ∀ n : ℕ, ∀ r : R, a ^ n * r = 0 → a ^ N * r = 0)
include h

/-- In the `(j+m)`-th quotient, the kernel of `a^m` maps into `(a^j)`
under multiplication by the original ring torsion bound. -/
theorem powerQuotient_mul_kernel_relation (j m : ℕ)
    (x : R ⧸ Ideal.span {a ^ (j + m)})
    (hx : (Ideal.Quotient.mk _ a) ^ m * x = 0) :
    ∃ y : R ⧸ Ideal.span {a ^ (j + m)},
      (Ideal.Quotient.mk _ a) ^ N * x = (Ideal.Quotient.mk _ a) ^ j * y := by
  let I : Ideal R := Ideal.span {a ^ (j + m)}
  let q := Ideal.Quotient.mk I
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : a ^ m * r ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp (by
    simpa only [map_mul, map_pow] using hx)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
  have he : a ^ m * (r - a ^ j * s) = 0 := by
    rw [mul_sub, ← mul_assoc, ← pow_add, add_comm m j, ← hs, sub_self]
  have hb := h m _ he
  have hb' : a ^ N * r = a ^ j * (a ^ N * s) := by
    rw [mul_sub] at hb
    exact (sub_eq_zero.mp hb).trans (by ring)
  refine ⟨q (a ^ N * s), ?_⟩
  simpa only [map_mul, map_pow] using congrArg q hb'

/-- Flatness over the actual power quotient transfers the ring relation to
arbitrary coefficient modules, with no finite generation assumption. -/
theorem flat_powerQuotient_torsion_relation (j m : ℕ) (M : Type*)
    [AddCommGroup M] [Module (R ⧸ Ideal.span {a ^ (j + m)}) M]
    [Module.Flat (R ⧸ Ideal.span {a ^ (j + m)}) M]
    (x : M) (hx : (Ideal.Quotient.mk (Ideal.span {a ^ (j + m)}) a) ^ m • x = 0) :
    ∃ y : M, (Ideal.Quotient.mk (Ideal.span {a ^ (j + m)}) a) ^ N • x =
      (Ideal.Quotient.mk (Ideal.span {a ^ (j + m)}) a) ^ j • y :=
  smul_eq_smul_of_flat_of_mul_kernel _ _ _
    (fun r hr ↦ powerQuotient_mul_kernel_relation a N h j m r hr) x hx

end SerrePositivity
