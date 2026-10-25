module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaStepIdentities
public import SerrePositivity.BhattScholze.Delta.Free.Finite.DeltaResidueArithmetic
public import SerrePositivity.BhattScholze.Delta.Free.RelativeDeltaEstimate

/-! # 有限δ計算の通常剰余公式

次の有限環からの通常射を明示し、pが消える場合の計算を行う。
有限剰余環のδ構造は要求しない。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- pを消す通常射の下で有限Frobenius計算は標準包含のp乗。 -/
theorem relativeFreeFiniteFrobeniusStep_map_of_prime_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteFrobeniusStep N σ D f) =
      (q (relativeFreeFiniteStepInclusion N σ f)) ^ p := by
  rw [relativeFreeFiniteFrobeniusStep_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]

/-- pを消す通常射の下で有限δ積の第三項は消える。 -/
theorem relativeFreeFiniteDeltaStep_map_mul_of_prime_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D (f * g)) =
      (q (relativeFreeFiniteStepInclusion N σ f)) ^ p * q (relativeFreeFiniteDeltaStep N σ D g) +
        q (relativeFreeFiniteDeltaStep N σ D f) *
          (q (relativeFreeFiniteStepInclusion N σ g)) ^ p := by
  exact wittTwoLift_map_delta_mul_of_prime_zero (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) q hp f g

/-- 左入力の包含像が消える通常射では有限δ加法の補正項も消える。 -/
theorem relativeFreeFiniteDeltaStep_map_add_of_left_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) (hf : q (relativeFreeFiniteStepInclusion N σ f) = 0) :
    q (relativeFreeFiniteDeltaStep N σ D (f + g)) =
      q (relativeFreeFiniteDeltaStep N σ D f) + q (relativeFreeFiniteDeltaStep N σ D g) := by
  exact wittTwoLift_map_delta_add_of_left_zero (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) q f g hf

/-- 右入力の包含像が消える場合の有限δ加法公式。 -/
theorem relativeFreeFiniteDeltaStep_map_add_of_right_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) (hg : q (relativeFreeFiniteStepInclusion N σ g) = 0) :
    q (relativeFreeFiniteDeltaStep N σ D (f + g)) =
      q (relativeFreeFiniteDeltaStep N σ D f) + q (relativeFreeFiniteDeltaStep N σ D g) := by
  exact wittTwoLift_map_delta_add_of_right_zero (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) q f g hg

/-- pを消す通常射の下での有限δ計算の正整数冪公式。 -/
theorem relativeFreeFiniteDeltaStep_map_pow_succ_of_prime_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) (m : ℕ) :
    q (relativeFreeFiniteDeltaStep N σ D (f ^ (m + 1))) =
      (m + 1 : ℕ) * (q (relativeFreeFiniteStepInclusion N σ f)) ^ (p * m) *
        q (relativeFreeFiniteDeltaStep N σ D f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp,
        map_pow, map_pow, ih]
      have he : ((q (relativeFreeFiniteStepInclusion N σ f)) ^ (m + 1)) ^ p =
          (q (relativeFreeFiniteStepInclusion N σ f)) ^ (p * m) *
            (q (relativeFreeFiniteStepInclusion N σ f)) ^ p := by
        rw [← pow_mul, Nat.add_mul, Nat.one_mul, Nat.mul_comm m p, pow_add]
      rw [he, Nat.mul_succ, pow_add]
      push_cast
      ring

/-- pを消す通常射の下で、有限δ計算のp乗の像は零。 -/
theorem relativeFreeFiniteDeltaStep_map_pow_prime_of_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D (f ^ p)) = 0 := by
  have hpB : (p : B) = 0 := by simpa only [map_natCast] using hp
  have he := relativeFreeFiniteDeltaStep_map_pow_succ_of_prime_zero N σ D q hp f (p - 1)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).pos] at he
  rw [he, hpB, zero_mul, zero_mul]

/-- pを消す通常射の下で、有限δ計算のδ(p)は1。 -/
theorem relativeFreeFiniteDeltaStep_map_prime_of_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0) :
    q (relativeFreeFiniteDeltaStep N σ D (p : MvPolynomial (σ × Fin (N + 1)) A)) = 1 := by
  have hp' : (q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 2)) A)) (p : A) = 0 := by
    simpa only [RingHom.comp_apply, map_natCast] using hp
  have he := D.map_delta_prime_of_zero (q.comp MvPolynomial.C) hp'
  rw [show (p : MvPolynomial (σ × Fin (N + 1)) A) = MvPolynomial.C (p : A) from
    (map_natCast (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A) p).symm,
    relativeFreeFiniteDeltaStep_C]
  exact he

end SerrePositivity.BhattScholze
