module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaResidue
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # 任意通常p剰余での有限δ像の最高偏微分

初期包含の最高偏微分が零であることから、実際のδ計算を微分する。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- 初期包含多項式には次段の最高変数が現れず、その偏微分は零。 -/
theorem relativeFreeFiniteStepInclusion_top_pderiv_zero (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    MvPolynomial.pderiv (s, Fin.last (N + 1)) (relativeFreeFiniteStepInclusion N σ f) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  change (s, Fin.last (N + 1)) ∈
    (MvPolynomial.rename (fun z : σ × Fin (N + 1) => (z.1, z.2.castSucc)) f).vars at h
  obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ h
  have hi := i.isLt
  have hv := congrArg (fun z : σ × Fin (N + 2) => z.2.val) he
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  omega

/-- 有限δ加法補正項は初期補正項の標準包含の像。 -/
theorem relativeFreeFiniteStepInclusion_additionCarry
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    (WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ f) +
      WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ g)).coeff 1 =
      relativeFreeFiniteStepInclusion N σ
        ((WittVector.teichmuller p f + WittVector.teichmuller p g).coeff 1) := by
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]

/-- 通常射の下で有限δ像の最高偏微分を取り出す。 -/
def relativeFreeFiniteDeltaTopDerivative (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : B :=
  q (MvPolynomial.pderiv (s, Fin.last (N + 1)) (relativeFreeFiniteDeltaStep N σ D f))

/-- 最高偏微分の像は加法的。 -/
theorem relativeFreeFiniteDeltaTopDerivative_add (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (f + g) =
      relativeFreeFiniteDeltaTopDerivative N σ D q s f +
        relativeFreeFiniteDeltaTopDerivative N σ D q s g := by
  unfold relativeFreeFiniteDeltaTopDerivative
  rw [relativeFreeFiniteDeltaStep_add, relativeFreeFiniteStepInclusion_additionCarry,
    map_add, map_add, relativeFreeFiniteStepInclusion_top_pderiv_zero,
    map_add, map_add, map_zero, add_zero]

/-- pを消す通常射の下での最高偏微分のFrobenius係数Leibniz公式。 -/
theorem relativeFreeFiniteDeltaTopDerivative_mul (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (f * g) =
      q (relativeFreeFiniteFrobeniusStep N σ D f) *
        relativeFreeFiniteDeltaTopDerivative N σ D q s g +
        relativeFreeFiniteDeltaTopDerivative N σ D q s f *
          q (relativeFreeFiniteFrobeniusStep N σ D g) := by
  have hf : MvPolynomial.pderiv (s, Fin.last (N + 1))
      ((relativeFreeFiniteStepInclusion N σ f) ^ p) = 0 := by
    rw [MvPolynomial.pderiv_pow, relativeFreeFiniteStepInclusion_top_pderiv_zero, mul_zero]
  have hg : MvPolynomial.pderiv (s, Fin.last (N + 1))
      ((relativeFreeFiniteStepInclusion N σ g) ^ p) = 0 := by
    rw [MvPolynomial.pderiv_pow, relativeFreeFiniteStepInclusion_top_pderiv_zero, mul_zero]
  have hprime : MvPolynomial.pderiv (s, Fin.last (N + 1))
      (p : MvPolynomial (σ × Fin (N + 2)) A) = 0 := by
    rw [show (p : MvPolynomial (σ × Fin (N + 2)) A) = MvPolynomial.C (p : A) from
      (map_natCast (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 2)) A) p).symm,
      MvPolynomial.pderiv_C]
  unfold relativeFreeFiniteDeltaTopDerivative
  rw [relativeFreeFiniteDeltaStep_mul]
  simp only [map_add, MvPolynomial.pderiv_mul, hf, hg, hprime, zero_mul, mul_zero,
    zero_add, add_zero, map_mul, map_pow, hp]
  rw [relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp,
    relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp]

/-- 係数の有限δ像の最高偏微分は零。 -/
@[simp] theorem relativeFreeFiniteDeltaTopDerivative_C (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s : σ) (a : A) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (MvPolynomial.C a) = 0 := by
  simp [relativeFreeFiniteDeltaTopDerivative]

/-- 各変数の最高偏微分の像は初期偏微分の有限Frobenius像。 -/
theorem relativeFreeFiniteDeltaTopDerivative_X (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s t : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (MvPolynomial.X (t, i)) =
      q (relativeFreeFiniteFrobeniusStep N σ D
        (MvPolynomial.pderiv (s, Fin.last N) (MvPolynomial.X (t, i)))) := by
  classical
  unfold relativeFreeFiniteDeltaTopDerivative
  rw [relativeFreeFiniteDeltaStep_X]
  by_cases hi : i = Fin.last N
  · subst i
    change q (MvPolynomial.pderiv (s, Fin.last (N + 1))
      (MvPolynomial.X (t, Fin.last (N + 1)))) = _
    by_cases ht : t = s
    · subst t
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X, ht, (Fact.out : p.Prime).ne_zero]
  · have hj : (t, i.succ) ≠ (s, Fin.last (N + 1)) := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg (fun z : σ × Fin (N + 2) => z.2.val) h
      simp only [Fin.val_succ, Fin.val_last] at hv
      simp only [Fin.val_last]
      omega
    have hj' : (t, i) ≠ (s, Fin.last N) := fun h => hi (congrArg Prod.snd h)
    rw [MvPolynomial.pderiv_X_of_ne hj, map_zero,
      MvPolynomial.pderiv_X_of_ne hj', map_zero, map_zero]

/-- 有限Frobenius射は基底係数上で基底Frobeniusに一致する。 -/
@[simp] theorem relativeFreeFiniteFrobeniusStep_C (D : DeltaStructure p A) (a : A) :
    relativeFreeFiniteFrobeniusStep N σ D (MvPolynomial.C a) =
      MvPolynomial.C (D.frobeniusLift a) := by
  simp [relativeFreeFiniteFrobeniusStep_apply, relativeFreeFiniteStepInclusion,
    DeltaStructure.frobeniusLift_apply]

/-- 任意通常p剰余で、最高偏微分は初期偏微分の有限Frobenius像。 -/
theorem relativeFreeFiniteDeltaTopDerivative_eq_frobenius_pderiv (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    q (MvPolynomial.pderiv (s, Fin.last (N + 1)) (relativeFreeFiniteDeltaStep N σ D f)) =
      q (relativeFreeFiniteFrobeniusStep N σ D (MvPolynomial.pderiv (s, Fin.last N) f)) := by
  change relativeFreeFiniteDeltaTopDerivative N σ D q s f = _
  induction f using MvPolynomial.induction_on with
  | C a => simp [(Fact.out : p.Prime).ne_zero]
  | add f g hf hg =>
      rw [relativeFreeFiniteDeltaTopDerivative_add, map_add, map_add, map_add, hf, hg]
  | mul_X f z hf =>
      obtain ⟨t, i⟩ := z
      rw [relativeFreeFiniteDeltaTopDerivative_mul N σ D q hp, MvPolynomial.pderiv_mul,
        map_add, map_add, map_mul, map_mul, map_mul, map_mul,
        relativeFreeFiniteDeltaTopDerivative_X, hf]
      ring

end SerrePositivity.BhattScholze
