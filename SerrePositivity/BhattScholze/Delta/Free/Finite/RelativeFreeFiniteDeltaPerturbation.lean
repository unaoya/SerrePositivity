module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaResidue

/-! # 有限δ計算におけるp倍・d倍の代表元補正

通常射がp,dを消す場合、補正のδ像をp乗の項として明示する。
有限商のδ安定性を仮定しない。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- p倍の補正は有限δ計算の後、包含像のp乗となる。 -/
theorem relativeFreeFiniteDeltaStep_map_prime_mul (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (g : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D ((p : MvPolynomial (σ × Fin (N + 1)) A) * g)) =
      (q (relativeFreeFiniteStepInclusion N σ g)) ^ p := by
  rw [relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp,
    map_natCast, hp, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul,
    relativeFreeFiniteDeltaStep_map_prime_of_zero N σ D q hp, one_mul, zero_add]

/-- 消える基底係数dの倍は、δ(d)係数付きのp乗となる。 -/
theorem relativeFreeFiniteDeltaStep_map_generator_mul (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (d : A) (hd : q (MvPolynomial.C d) = 0)
    (h : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C d * h)) =
      q (MvPolynomial.C (D.delta d)) *
        (q (relativeFreeFiniteStepInclusion N σ h)) ^ p := by
  rw [relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp]
  have hC : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d) = MvPolynomial.C d := by
    change MvPolynomial.rename _ (MvPolynomial.C d) = _
    exact MvPolynomial.rename_C _ d
  rw [hC, hd, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, zero_add,
    relativeFreeFiniteDeltaStep_C]

/-- p倍・d倍による代表元の変更は、二つの明示的p乗項を加える。 -/
theorem relativeFreeFiniteDeltaStep_map_perturbation (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (d : A) (hd : q (MvPolynomial.C d) = 0)
    (f g h : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D
      (f + (p : MvPolynomial (σ × Fin (N + 1)) A) * g + MvPolynomial.C d * h)) =
      q (relativeFreeFiniteDeltaStep N σ D f) +
        (q (relativeFreeFiniteStepInclusion N σ g)) ^ p +
          q (MvPolynomial.C (D.delta d)) *
            (q (relativeFreeFiniteStepInclusion N σ h)) ^ p := by
  have hpg : q (relativeFreeFiniteStepInclusion N σ
      ((p : MvPolynomial (σ × Fin (N + 1)) A) * g)) = 0 := by
    rw [map_mul, map_mul, map_natCast, hp, zero_mul]
  have hdh : q (relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d * h)) = 0 := by
    rw [map_mul, map_mul]
    have hC : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d) = MvPolynomial.C d := by
      change MvPolynomial.rename _ (MvPolynomial.C d) = _
      exact MvPolynomial.rename_C _ d
    rw [hC, hd, zero_mul]
  rw [relativeFreeFiniteDeltaStep_map_add_of_right_zero N σ D q _ _ hdh,
    relativeFreeFiniteDeltaStep_map_add_of_right_zero N σ D q _ _ hpg,
    relativeFreeFiniteDeltaStep_map_prime_mul N σ D q hp,
    relativeFreeFiniteDeltaStep_map_generator_mul N σ D q hp d hd]

end SerrePositivity.BhattScholze
