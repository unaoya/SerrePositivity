module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedFrobenius
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：実際の局所化の Frobenius を、指定次数の斉次局所化へ制限する。
方針：分数の指数を p 倍し、分子の次数が p 倍になることを示す。
規約：局所化が零環の場合も含め、元の基底環の Frobenius について半線形とする。
使われ方：構造層の標準開と Čech の Frobenius、閉厚化の指数移動への入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
variable {R P A : Type*} [CommRing R] [CommRing P] [CommRing A]
variable [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
variable (p : ℕ) (hp : p.Prime) [ExpChar R p]
variable (f : P) (V W : ℕ → Submodule R A)

/-- Frobenius は、分子の p 乗が対応する指定部分へ入る場合に斉次局所化へ降りる。 -/
def projectiveGradedAwayFrobenius (hz : (p : A) = 0)
    (hstep : ∀ n (m : V n), f • m.val ∈ V (n + 1))
    (hpow : ∀ n (m : V n), m.val ^ p ∈ W (p * n)) :
    projectiveGradedAway f V →ₛₗ[frobenius R p] projectiveGradedAway f W := by
  let F := projectiveLocalizedFrobeniusSemilinear (R := R) p hp (Submonoid.powers f) hz
  have hmem : ∀ z : projectiveGradedAway f V, F z.val ∈ projectiveGradedAway f W := by
    intro z
    obtain ⟨n, m, hm⟩ := (mem_projectiveGradedAway_iff f V hstep z.val).mp z.property
    apply (le_iSup (fun k ↦ LinearMap.range (projectiveGradedFraction f W k)) (p * n))
    refine ⟨⟨m.val ^ p, hpow n m⟩, ?_⟩
    change projectiveGradedFraction f W (p * n) _ =
      projectiveLocalizedFrobenius p hp (Submonoid.powers f) hz z.val
    rw [← hm, projectiveGradedFraction_apply, projectiveGradedFraction_apply]
    exact (projectiveLocalizedFrobenius_fraction p hp f hz m.val n).symm
  exact (F.domRestrict (projectiveGradedAway f V)).codRestrict _ hmem

/-- 斉次局所化の Frobenius は、周囲の実際の局所化の Frobenius の制限。 -/
theorem projectiveGradedAwayFrobenius_val (hz : (p : A) = 0)
    (hstep : ∀ n (m : V n), f • m.val ∈ V (n + 1))
    (hpow : ∀ n (m : V n), m.val ^ p ∈ W (p * n))
    (z : projectiveGradedAway f V) :
    (projectiveGradedAwayFrobenius p hp f V W hz hstep hpow z).val =
      projectiveLocalizedFrobenius p hp (Submonoid.powers f) hz z.val := rfl

section Grading
variable (G : ℕ → Submodule R A) [SetLike.GradedMonoid G]

/-- 自然数次数を整数へ零延長した後も、p 乗は Proj 次数を p 倍する。 -/
theorem projectiveNatGradingInt_pow_mem (j : ℤ) (m : A)
    (hm : m ∈ projectiveNatGradingInt G j) :
    m ^ p ∈ projectiveNatGradingInt G ((p : ℤ) * j) := by
  by_cases hj : 0 ≤ j
  · have hm' : m ∈ G j.toNat := by simpa only [projectiveNatGradingInt, hj, ite_true] using hm
    have hpow := SetLike.pow_mem_graded p hm'
    have hc : (p : ℤ) * j = ((p * j.toNat : ℕ) : ℤ) := by
      calc
        (p : ℤ) * j = (p : ℤ) * (j.toNat : ℤ) :=
          congrArg (fun t : ℤ ↦ (p : ℤ) * t) (Int.toNat_of_nonneg hj).symm
        _ = _ := (Nat.cast_mul p j.toNat).symm
    rw [hc, projectiveNatGradingInt_natCast]
    simpa only [nsmul_eq_mul, Nat.cast_id] using hpow
  · have hmzero : m = 0 := by
      simpa only [projectiveNatGradingInt, hj, ite_false, Submodule.mem_bot] using hm
    rw [hmzero, zero_pow (Nat.ne_of_gt (expChar_pos R p))]
    exact Submodule.zero_mem _

/-- 指定分母の n 冪の分子の p 乗は、p 倍の捻りと p*n 冪の分母に対応する。 -/
theorem projectiveNatGradingInt_chart_pow_mem (d δ : ℤ) (n : ℕ)
    (m : projectiveNatGradingInt G (d + n • δ)) :
    m.val ^ p ∈ projectiveNatGradingInt G ((p : ℤ) * d + (p * n) • δ) := by
  have h := projectiveNatGradingInt_pow_mem p G (d + n • δ) m.val m.property
  have he : (p : ℤ) * (d + n • δ) = (p : ℤ) * d + (p * n) • δ := by
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  exact he ▸ h

end Grading
end SerrePositivity.AlgebraicGeometry
