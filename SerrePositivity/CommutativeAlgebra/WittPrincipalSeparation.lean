module

public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.Algebra.Regular.Basic

/-! # 第0係数によるWitt環の主イデアル進分離性 -/

@[expose] public noncomputable section
namespace SerrePositivity
variable (k : Type*) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- 第0係数が正則でその主イデアルに関して分離なら、Witt元に関しても分離。 -/
theorem witt_isHausdorff_of_constantCoeff (d : WittVector p k)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x))
    [IsHausdorff (Ideal.span {d.coeff 0}) k] :
    IsHausdorff (Ideal.span {d}) (WittVector p k) := by
  let C : WittVector p k →+* k := WittVector.constantCoeff
  have hcoeff (x : WittVector p k) (hx : ∀ n : ℕ, d ^ n ∣ x) : x.coeff 0 = 0 := by
    apply IsHausdorff.haus' (I := Ideal.span {d.coeff 0})
    intro n
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    apply SModEq.sub_mem.mpr
    simp only [sub_zero]
    obtain ⟨z, hz⟩ := hx n
    exact Ideal.mem_span_singleton.mpr
      ⟨C z, by simpa only [map_mul, map_pow, C, WittVector.constantCoeff_apply] using congrArg C hz⟩
  have hpreg : Function.Injective (fun x : WittVector p k ↦ (p : WittVector p k) * x) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply WittVector.eq_zero_of_p_mul_eq_zero
    simpa only [sub_mul, mul_comm] using sub_eq_zero.mpr hxy
  have hdivide (x : WittVector p k) (hx : ∀ n : ℕ, d ^ n ∣ x) :
      ∃ y, (p : WittVector p k) * y = x ∧ ∀ n : ℕ, d ^ n ∣ y := by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp
      ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).mpr (hcoeff x hx))
    refine ⟨y, hy.symm, ?_⟩
    intro n
    obtain ⟨z, hz⟩ := hx n
    have hcz : z.coeff 0 = 0 := by
      have h := congrArg C hz
      change x.coeff 0 = C (d ^ n * z) at h
      rw [map_mul, map_pow, hcoeff x hx] at h
      apply (IsLeftRegular.pow n hreg)
      change d.coeff 0 ^ n * z.coeff 0 = d.coeff 0 ^ n * 0
      simpa only [mul_zero, C, WittVector.constantCoeff_apply] using h.symm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp
      ((WittVector.mem_span_p_iff_coeff_zero_eq_zero z).mpr hcz)
    refine ⟨w, hpreg ?_⟩
    change (p : WittVector p k) * y = (p : WittVector p k) * (d ^ n * w)
    rw [← hy, hz, hw]
    ring
  have hpow (n : ℕ) (x : WittVector p k) (hx : ∀ m : ℕ, d ^ m ∣ x) :
      (p : WittVector p k) ^ n ∣ x := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      obtain ⟨y, hy, hdy⟩ := hdivide x hx
      obtain ⟨z, hz⟩ := ih y hdy
      refine ⟨z, ?_⟩
      rw [← hy, hz, pow_succ']
      ring
  constructor
  intro x hx
  have hdx (n : ℕ) : d ^ n ∣ x := by
    have h := SModEq.sub_mem.mp (hx n)
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h
    exact Ideal.mem_span_singleton.mp (by simpa only [sub_zero] using h)
  apply IsHausdorff.haus' (I := Ideal.span {(p : WittVector p k)})
  intro n
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero] using Ideal.mem_span_singleton.mpr (hpow n x hdx)

end SerrePositivity
