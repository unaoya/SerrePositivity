module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # 素イデアルの商上の非零因子

素イデアルの外の元は、商を元の環上の加群として見たときも正則に作用する。
局所性・Noether 性・Hilbert–Samuel 理論は必要ない。
-/

@[expose] public section

namespace SerrePositivity

variable {R : Type*} [CommRing R]

/-- 素イデアルの外の元は、その素イデアルによる商に正則に作用する。 -/
theorem isSMulRegular_quotient_of_notMem_prime (p : Ideal R) [p.IsPrime]
    {x : R} (hx : x ∉ p) : IsSMulRegular (R ⧸ p) x := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro y hxy
  exact (‹p.IsPrime›.mem_or_mem (show x * y ∈ p from hxy)).resolve_left hx

/-- 素イデアルによる商に正則に作用する元は、ちょうどその素イデアルの外の元。 -/
theorem isSMulRegular_quotient_iff_notMem_prime (p : Ideal R) [p.IsPrime] (x : R) :
    IsSMulRegular (R ⧸ p) x ↔ x ∉ p := by
  refine ⟨fun h hx ↦ ?_, isSMulRegular_quotient_of_notMem_prime p⟩
  have hone : (1 : R) ∈ p :=
    (isSMulRegular_quotient_iff_mem_of_smul_mem p x).mp h 1 (by simpa using hx)
  exact ‹p.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem p hone isUnit_one)

end SerrePositivity
