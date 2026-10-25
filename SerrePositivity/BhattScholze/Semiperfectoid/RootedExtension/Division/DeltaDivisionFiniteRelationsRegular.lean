module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteStageTailQuotient
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.Logic.Equiv.Option

/-! # 一般除数の次δ関係の正則性

初期有限関係商と後続変数表示を用い、先頭係数φ^(N+1)(d)の正則性から
次の実反復δ関係の正則性を得る。完備性・ghost単射は要求しない。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

private theorem linear_polynomial_regular {R : Type u} [CommRing R] (c b : R)
    (hc : Function.Injective (fun x : R => c * x)) :
    Function.Injective (fun x : Polynomial R =>
      (Polynomial.C c * Polynomial.X + Polynomial.C b) * x) := by
  nontriviality R
  have hc₀ : c ≠ 0 := by
    intro h
    have he : c * (1 : R) = c * 0 := by simp [h]
    exact one_ne_zero (hc he)
  have hp : (Polynomial.C c * Polynomial.X + Polynomial.C b) ∈
      nonZeroDivisors (Polynomial R) := by
    apply Polynomial.mem_nonZeroDivisors_of_leadingCoeff
    rw [Polynomial.leadingCoeff_linear hc₀]
    exact mem_nonZeroDivisors_iff_left.mpr fun x hx => hc (hx.trans (mul_zero c).symm)
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hp).left

private theorem linear_mvpolynomial_regular {R : Type u} [CommRing R] {τ : Type v}
    (c b : R) (s : τ) (hc : Function.Injective (fun x : R => c * x)) :
    IsSMulRegular (MvPolynomial τ R) (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : τ // t ≠ s})
  have he : e (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C c) * Polynomial.X + Polynomial.C (MvPolynomial.C b) := by
    simp [e, MvPolynomial.renameEquiv]
  have hc' := (show IsSMulRegular R c from hc).of_flat
    (S := MvPolynomial {t : τ // t ≠ s} R)
  have hr := linear_polynomial_regular (MvPolynomial.C c) (MvPolynomial.C b) hc'
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a

/-- 除数dが正則なら、任意元の最初の実除算関係は自由δ環上で非零因子。 -/
theorem deltaDivisionFirstRelation_isSMulRegular (s : σ)
    (hd : IsSMulRegular A d) :
    IsSMulRegular L₀ (deltaDivisionIteratedRelation D d a s 0) := by
  change IsSMulRegular L₀ (MvPolynomial.C d * MvPolynomial.X (s, 0) - MvPolynomial.C (a s))
  rw [sub_eq_add_neg, ← map_neg]
  exact linear_mvpolynomial_regular d (-(a s)) (s, 0) hd

/-- 前段商での先頭係数の正則性は、初期有限関係商の同じ係数へ降りる。 -/
theorem deltaDivisionFiniteStageInitialQuotient_coefficient_isSMulRegular (N : ℕ) (c : A)
    (hc : IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (MvPolynomial.C c))) :
    IsSMulRegular (MvPolynomial (σ × Fin (N + 1)) A ⧸
      deltaDivisionFiniteStageInitialIdeal D d a N)
      (Ideal.Quotient.mk (deltaDivisionFiniteStageInitialIdeal D d a N) (MvPolynomial.C c)) := by
  let J := deltaDivisionFiniteStageInitialIdeal D d a N
  let B := MvPolynomial (σ × Fin (N + 1)) A ⧸ J
  let e := deltaDivisionFiniteStageTailQuotientEquiv D d a N
  have he : e (Ideal.Quotient.mk (I₀ N) (MvPolynomial.C c)) =
      MvPolynomial.C (Ideal.Quotient.mk J (MvPolynomial.C c)) := by
    rw [deltaDivisionFiniteStageTailQuotientEquiv_mk,
      relativeFreeFiniteVariableSplitAlgEquiv_C, MvPolynomial.map_C]
  have hc' : IsSMulRegular (MvPolynomial (σ × ℕ) B)
      (MvPolynomial.C (σ := σ × ℕ) (Ideal.Quotient.mk J (MvPolynomial.C c))) := by
    intro x y h
    apply e.symm.injective
    apply hc
    apply e.injective
    simpa only [smul_eq_mul, map_mul, he, e.apply_symm_apply] using h
  intro x y h
  apply (MvPolynomial.C_injective (σ := σ × ℕ))
  apply hc'
  simpa only [smul_eq_mul, map_mul] using
    congrArg (MvPolynomial.C : B →+* MvPolynomial (σ × ℕ) B) h

/-- 前段商のφ^(N+1)(d)係数像が正則なら、次の実δ関係はその商上で非零因子。 -/
theorem deltaDivisionFiniteStage_next_isSMulRegular_of_frobenius_regular (N : ℕ) (s : σ)
    (hc : IsSMulRegular (L₀ ⧸ I₀ N)
      (Ideal.Quotient.mk (I₀ N) (MvPolynomial.C (D.frobeniusLift^[N + 1] d)))) :
    IsSMulRegular (L₀ ⧸ I₀ N)
      (Ideal.Quotient.mk (I₀ N) (deltaDivisionIteratedRelation D d a s (N + 1))) := by
  let J := deltaDivisionFiniteStageInitialIdeal D d a N
  let e := deltaDivisionFiniteStageTailQuotientEquiv D d a N
  have hc' := deltaDivisionFiniteStageInitialQuotient_coefficient_isSMulRegular D d a N
    (D.frobeniusLift^[N + 1] d) hc
  have hr := linear_mvpolynomial_regular (Ideal.Quotient.mk J
    (MvPolynomial.C (D.frobeniusLift^[N + 1] d)))
    (Ideal.Quotient.mk J (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1)))
    (s, 0) hc'
  have he := deltaDivisionFiniteStageTailQuotientEquiv_next D d a N s
  change e (Ideal.Quotient.mk (I₀ N) (deltaDivisionIteratedRelation D d a s (N + 1))) = _ at he
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

end SerrePositivity.BhattScholze
