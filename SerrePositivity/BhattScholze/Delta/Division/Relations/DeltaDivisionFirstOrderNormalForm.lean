module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaSubtraction
public import SerrePositivity.BhattScholze.Delta.Division.Relations.DeltaDivisionFiniteRelationPolynomial
public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaSquareCongruence

/-! # 第一δ除算関係式の二次誤差を含む具体的正規形

減算補正をイデアルの二乗で追い、次のδ計算へ渡せる代表元を示す。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 基底係数倍の有限δ像を、基底Frobeniusとδの係数で正確に表す。 -/
theorem relativeFreeFiniteDeltaStep_coefficient_mul (N : ℕ) (D : DeltaStructure p A)
    (d : A) (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C d * f) =
      MvPolynomial.C (D.frobeniusLift d) * relativeFreeFiniteDeltaStep N σ D f +
        MvPolynomial.C (D.delta d) * (relativeFreeFiniteStepInclusion N σ f) ^ p := by
  have hC : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d) = MvPolynomial.C d := by
    change MvPolynomial.rename _ (MvPolynomial.C d) = _
    exact MvPolynomial.rename_C _ d
  rw [relativeFreeFiniteDeltaStep_mul, hC, relativeFreeFiniteDeltaStep_C,
    D.frobeniusLift_apply, map_add, map_mul, map_pow, map_natCast]
  ring

/-- 通常除算関係式の有限δ像の正規形からの差は、二入力を含むイデアルの二乗。 -/
theorem relativeFreeFiniteDeltaStep_division_normalForm_mem_square (N : ℕ)
    (D : DeltaStructure p A) (d a : A) (f : MvPolynomial (σ × Fin (N + 1)) A)
    (I : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (hd : MvPolynomial.C d ∈ I) (ha : MvPolynomial.C a ∈ I) :
    relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C d * f - MvPolynomial.C a) -
      (MvPolynomial.C (D.frobeniusLift d) * relativeFreeFiniteDeltaStep N σ D f +
        MvPolynomial.C (D.delta d) * (relativeFreeFiniteStepInclusion N σ f) ^ p -
          MvPolynomial.C (D.delta a)) ∈ I ^ 2 := by
  have hC (z : A) : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C z) = MvPolynomial.C z := by
    change MvPolynomial.rename _ (MvPolynomial.C z) = _
    exact MvPolynomial.rename_C _ z
  have hdf : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d * f) ∈ I := by
    rw [map_mul, hC]
    exact I.mul_mem_right _ hd
  have he := relativeFreeFiniteDeltaStep_sub_error_mem_square N σ D I
    (MvPolynomial.C d * f) (MvPolynomial.C a) hdf (by simpa only [hC] using ha)
  rw [relativeFreeFiniteDeltaStep_coefficient_mul, relativeFreeFiniteDeltaStep_C] at he
  exact he

/-- 第一反復関係式を具体的な二次誤差付き正規形にする、全段帰納の初期段。 -/
theorem deltaDivisionFiniteRelationPolynomial_one_normalForm_mem_square
    (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ)
    (I : Ideal (MvPolynomial (σ × Fin 2) A))
    (hd : MvPolynomial.C d ∈ I) (ha : MvPolynomial.C (a s) ∈ I) :
    deltaDivisionFiniteRelationPolynomial D d a s 1 -
      (MvPolynomial.C (D.frobeniusLift d) * MvPolynomial.X (s, 1) +
        MvPolynomial.C (D.delta d) * MvPolynomial.X (s, 0) ^ p -
          MvPolynomial.C (D.delta (a s))) ∈ I ^ 2 := by
  have he := relativeFreeFiniteDeltaStep_division_normalForm_mem_square 0 D d (a s)
    (MvPolynomial.X (s, 0)) I hd ha
  simpa [deltaDivisionFiniteRelationPolynomial, relativeFreeFiniteDeltaStep_X,
    relativeFreeFiniteStepInclusion] using he

/-- 第二反復関係式の通常p剰余像は、第一段の具体的正規形にδを適用して計算できる。 -/
theorem deltaDivisionFiniteRelationPolynomial_two_image_of_normalForm
    {B : Type w} [CommRing B] (D : DeltaStructure p A) (d : A) (a : σ → A) (s : σ)
    (q : MvPolynomial (σ × Fin 3) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin 3) A) = 0)
    (hd : q (MvPolynomial.C d) = 0) (ha : q (MvPolynomial.C (a s)) = 0) :
    q (deltaDivisionFiniteRelationPolynomial D d a s 2) =
      q (relativeFreeFiniteDeltaStep 1 σ D
        (MvPolynomial.C (D.frobeniusLift d) * MvPolynomial.X (s, 1) +
          MvPolynomial.C (D.delta d) * MvPolynomial.X (s, 0) ^ p -
            MvPolynomial.C (D.delta (a s)))) := by
  rw [deltaDivisionFiniteRelationPolynomial_succ]
  apply relativeFreeFiniteDeltaStep_map_eq_of_sub_mem_ker_square 1 σ D q hp
  apply deltaDivisionFiniteRelationPolynomial_one_normalForm_mem_square
  · change q (relativeFreeFiniteStepInclusion 1 σ (MvPolynomial.C d)) = 0
    simpa [relativeFreeFiniteStepInclusion] using hd
  · change q (relativeFreeFiniteStepInclusion 1 σ (MvPolynomial.C (a s))) = 0
    simpa [relativeFreeFiniteStepInclusion] using ha

end SerrePositivity.BhattScholze
