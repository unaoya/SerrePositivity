module

public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：自然数次数を k 倍する写像を、零延長した整数次数と標準開の捻りへ移す。
方針：非負の次数は自然数へ戻し、負の次数の元は零であることを使う。
規約：k=0 も許し、乗法構造は要求しない。
使われ方：厚化 Frobenius の商環の次数制御を斉次局所化へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N) (f : M →+ N) (k : ℕ)
variable (hf : ∀ n x, x ∈ G n → f x ∈ H (k * n))

include hf in
/-- 自然数次数を k 倍する加法写像は、零延長した整数次数も k 倍する。 -/
theorem projectiveNatGradingInt_map_mem_mul (j : ℤ) (x : M)
    (hx : x ∈ projectiveNatGradingInt G j) :
    f x ∈ projectiveNatGradingInt H ((k : ℤ) * j) := by
  by_cases hj : 0 ≤ j
  · have hx' : x ∈ G j.toNat := by
      simpa only [projectiveNatGradingInt, hj, ite_true] using hx
    have hc : (k : ℤ) * j = ((k * j.toNat : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Int.toNat_of_nonneg hj]
    rw [hc, projectiveNatGradingInt_natCast]
    exact hf j.toNat x hx'
  · have hx0 : x = 0 := by
      simpa only [projectiveNatGradingInt, hj, ite_false, Submodule.mem_bot] using hx
    rw [hx0, map_zero]
    exact Submodule.zero_mem _

include hf in
/-- 標準開で分母の指数を k 倍すると、捻りも k 倍になる。 -/
theorem projectiveNatGradingInt_chart_map_mem_mul (d δ : ℤ) (n : ℕ)
    (x : projectiveNatGradingInt G (d + n • δ)) :
    f x.val ∈ projectiveNatGradingInt H ((k : ℤ) * d + (k * n) • δ) := by
  have hx := projectiveNatGradingInt_map_mem_mul G H f k hf (d + n • δ) x.val x.property
  have he : (k : ℤ) * (d + n • δ) = (k : ℤ) * d + (k * n) • δ := by
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  exact he ▸ hx

end SerrePositivity.AlgebraicGeometry
