module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaTopDerivative
public import SerrePositivity.BhattScholze.DeltaDivisionFiniteRelationPolynomial

/-! # 全反復除算関係式の最高偏微分のp剰余像

任意深さの最高偏微分を、基底Frobeniusの反復で表す。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B] {σ : Type v}
attribute [local instance] Classical.propDecidable

/-- 任意深さの除算関係式の最高偏微分は、通常p剰余でφ^n(d)となる。
対応しない生成元の最高偏微分は零。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0) (s : σ) :
    q (MvPolynomial.pderiv (s, Fin.last n) (deltaDivisionFiniteRelationPolynomial D d a t n)) =
      if s = t then q (MvPolynomial.C (D.frobeniusLift^[n] d)) else 0 := by
  classical
  induction n with
  | zero =>
      by_cases h : s = t
      · subst t
        simp [deltaDivisionFiniteRelationPolynomial, MvPolynomial.pderiv_X]
      · simp [deltaDivisionFiniteRelationPolynomial, MvPolynomial.pderiv_X, h]
  | succ n ih =>
      rw [deltaDivisionFiniteRelationPolynomial_succ,
        relativeFreeFiniteDeltaTopDerivative_eq_frobenius_pderiv n σ D q hp]
      let q₀ := q.comp (relativeFreeFiniteFrobeniusStep n σ D)
      have hp₀ : q₀ (p : MvPolynomial (σ × Fin (n + 1)) A) = 0 := by
        simpa only [q₀, RingHom.comp_apply, map_natCast] using hp
      have he := ih q₀ hp₀
      change q₀ (MvPolynomial.pderiv (s, Fin.last n)
        (deltaDivisionFiniteRelationPolynomial D d a t n)) = _
      rw [he]
      split_ifs with h
      · change q (relativeFreeFiniteFrobeniusStep n σ D
          (MvPolynomial.C (D.frobeniusLift^[n] d))) = _
        rw [relativeFreeFiniteFrobeniusStep_C, Function.iterate_succ_apply']
      · rfl

/-- 対応する生成元の最高偏微分はφ^n(d)の係数像。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative_self
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0) :
    q (MvPolynomial.pderiv (t, Fin.last n) (deltaDivisionFiniteRelationPolynomial D d a t n)) =
      q (MvPolynomial.C (D.frobeniusLift^[n] d)) := by
  simpa using deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n q hp t

/-- 別の生成元の最高偏微分は零。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative_of_ne
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0) (s : σ) (hs : s ≠ t) :
    q (MvPolynomial.pderiv (s, Fin.last n)
      (deltaDivisionFiniteRelationPolynomial D d a t n)) = 0 := by
  simpa only [ite_eq_right hs] using
    deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n q hp s

/-- p,dを消す通常射では全反復関係式の最高偏微分の像は零。 -/
theorem deltaDivisionFiniteRelationPolynomial_top_derivative_of_prime_generator_zero
    (D : DeltaStructure p A) (d : A) (a : σ → A) (t : σ) (n : ℕ)
    (q : MvPolynomial (σ × Fin (n + 1)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (n + 1)) A) = 0)
    (hd : q (MvPolynomial.C d) = 0) (s : σ) :
    q (MvPolynomial.pderiv (s, Fin.last n)
      (deltaDivisionFiniteRelationPolynomial D d a t n)) = 0 := by
  let f := q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (n + 1)) A)
  have hp' : f (p : A) = 0 := by
    simpa only [f, RingHom.comp_apply, map_natCast] using hp
  have hz (m : ℕ) : f (D.frobeniusLift^[m] d) = 0 := by
    induction m with
    | zero => exact hd
    | succ m ih =>
        rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow, map_mul,
          hp', ih, zero_mul, add_zero, zero_pow (Fact.out : p.Prime).ne_zero]
  rw [deltaDivisionFiniteRelationPolynomial_top_derivative D d a t n q hp s]
  split_ifs
  · exact hz n
  · rfl

end SerrePositivity.BhattScholze
