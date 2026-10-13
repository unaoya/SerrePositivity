module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # 主イデアル完備化上の生成元の正則性

生成元が正則なら、完備化上でも正則である。逆極限の一段先の座標で直接証明する。
根の塔・Noether 性・平坦性には依存しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

/-- 正則元が生成する主イデアルについて、完備化上でもその元は正則。
第 `n+1` 座標で生成元をキャンセルし、第 `n` 座標が零であることを示す。 -/
theorem isSMulRegular_adicCompletion_span_singleton
    (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a) :
    IsSMulRegular (AdicCompletion (Ideal.span {a}) R)
      (algebraMap R (AdicCompletion (Ideal.span {a}) R) a) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨v, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {a}) R x
  apply AdicCompletion.ext_evalₐ
  intro n
  have hx' : a * v.val (n + 1) ∈ (Ideal.span {a}) ^ (n + 1) := by
    have he := congrArg (AdicCompletion.evalₐ (Ideal.span {a}) (n + 1)) hx
    change Ideal.Quotient.mk ((Ideal.span {a}) ^ (n + 1)) (a * v.val (n + 1)) = 0 at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx'
  obtain ⟨z, hz⟩ := hx'
  have hv : v.val (n + 1) = a ^ n * z := by
    apply ha
    change a * v.val (n + 1) = a * (a ^ n * z)
    simpa [pow_succ', mul_assoc] using hz
  have hvmem : v.val (n + 1) ∈ (Ideal.span {a}) ^ n := by
    rw [hv, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have hdelta := v.property (Nat.le_succ n)
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hdelta
  have hn : v.val n ∈ (Ideal.span {a}) ^ n := by
    simpa using (Ideal.span {a} ^ n).add_mem hdelta hvmem
  simpa only [AdicCompletion.evalₐ_mk, map_zero] using
    Ideal.Quotient.eq_zero_iff_mem.mpr hn

end SerrePositivity
