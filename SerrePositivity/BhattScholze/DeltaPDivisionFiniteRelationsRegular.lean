module

public import SerrePositivity.BhattScholze.DeltaDivisionFiniteStageTailQuotient
public import SerrePositivity.BhattScholze.DeltaPDivisionFiniteStageRegular
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Logic.Equiv.Option

/-! # 実一元p除算関係の非零因子性

最高係数pの正則性と後続変数表示を用いる。mod pでの正則性だけからは結論しない。
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
  intro x y h
  change (Polynomial.C c * Polynomial.X + Polynomial.C b) * x =
    (Polynomial.C c * Polynomial.X + Polynomial.C b) * y at h
  apply sub_eq_zero.mp
  by_contra hxy
  have hz : (Polynomial.C c * Polynomial.X + Polynomial.C b) * (x - y) = 0 := by
    rw [mul_sub, h, sub_self]
  have hl : c * (x - y).leadingCoeff ≠ 0 := by
    intro he
    have he' : c * (x - y).leadingCoeff = c * 0 := by simpa using he
    exact hxy (Polynomial.leadingCoeff_eq_zero.mp (hc he'))
  have hl' : (Polynomial.C c * Polynomial.X + Polynomial.C b).leadingCoeff *
      (x - y).leadingCoeff ≠ 0 := by
    simpa only [Polynomial.leadingCoeff_linear hc₀] using hl
  have he := Polynomial.leadingCoeff_mul' hl'
  rw [hz, Polynomial.leadingCoeff_zero, Polynomial.leadingCoeff_linear hc₀] at he
  exact hl he.symm

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

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) a₀ (default : σ)
local notation "I₀" => deltaDivisionFiniteRelationIdeal D (p : A) a₀

/-- 最初の実p除算関係は、Aのp正則性だけで自由δ環上の非零因子。 -/
theorem deltaPDivisionFirstRelation_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x)) :
    IsSMulRegular L₀ (g₀ 0) := by
  change IsSMulRegular L₀
    (MvPolynomial.C (p : A) * MvPolynomial.X (default, 0) - MvPolynomial.C (D.frobeniusLift y))
  rw [sub_eq_add_neg, ← map_neg]
  exact linear_mvpolynomial_regular (p : A) (-(D.frobeniusLift y)) (default, 0) hpA

/-- 前段実関係商がp正則なら、次の実p除算関係はその商上で非零因子。 -/
theorem deltaPDivisionFiniteStage_next_isSMulRegular_of_p_regular (N : ℕ)
    (hpQ : Function.Injective (fun x : L₀ ⧸ I₀ N => (p : _) * x)) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1))) := by
  let J := deltaDivisionFiniteStageInitialIdeal D (p : A) a₀ N
  let B := MvPolynomial (σ × Fin (N + 1)) A ⧸ J
  let e := deltaDivisionFiniteStageTailQuotientEquiv D (p : A) a₀ N
  have hpB := deltaDivisionFiniteStageInitialQuotient_p_mul_injective D (p : A) a₀ N hpQ
  have hφ : D.frobeniusLift^[N + 1] (p : A) = p := by
    have aux : ∀ n : ℕ, D.frobeniusLift^[n] (p : A) = p := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, map_natCast]
    exact aux _
  have he := deltaDivisionFiniteStageTailQuotientEquiv_next D (p : A) a₀ N (default : σ)
  rw [hφ, map_natCast (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A) p,
    map_natCast (Ideal.Quotient.mk J) p] at he
  change e (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1))) = _ at he
  have hr := linear_mvpolynomial_regular (p : B)
    (Ideal.Quotient.mk J (deltaDivisionFiniteLeadingLowerPolynomial D (p : A) a₀ default (N + 1)))
    ((default : σ), 0) hpB
  intro x z h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

/-- 正則な一元入力の全有限段で、次の実δ関係は通常商上の非零因子。
単元δ(p)とghost単射は既存p正則性の中間入力として保持する。 -/
theorem deltaPDivisionFiniteStage_next_isSMulRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    IsSMulRegular (L₀ ⧸ I₀ N) (Ideal.Quotient.mk (I₀ N) (g₀ (N + 1))) :=
  deltaPDivisionFiniteStage_next_isSMulRegular_of_p_regular D y N
    (deltaPDivisionFiniteStage_quotient_p_mul_injective D y hpA hg v hv hy N)

/-- 全有限実関係列の生成イデアルは、既存の全有限段関係イデアル。 -/
theorem deltaPDivisionFiniteRelations_ofList (N : ℕ) :
    Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) = I₀ N := by
  unfold Ideal.ofList deltaDivisionFiniteRelationIdeal
  congr 1
  ext z
  simp only [List.mem_ofFn, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(default, i), rfl⟩
  · rintro ⟨⟨s, i⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact ⟨i, rfl⟩

/-- pを前置しない実δ関係列自身の弱正則性。 -/
theorem deltaPDivisionFiniteRelations_isWeaklyRegular
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular L₀ (List.ofFn fun i : Fin (N + 1) => g₀ i.val) := by
  induction N with
  | zero =>
      simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero] using
        (RingTheory.Sequence.isWeaklyRegular_singleton_iff L₀ (g₀ 0)).mpr
          (deltaPDivisionFirstRelation_isSMulRegular D y hpA)
  | succ N ih =>
      rw [List.ofFn_succ', List.concat_eq_append,
        RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨ih, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) • ⊤ :
          Submodule L₀ L₀) = I₀ N := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top, deltaPDivisionFiniteRelations_ofList]
      change IsSMulRegular (L₀ ⧸
        (Ideal.ofList (List.ofFn fun i : Fin (N + 1) => g₀ i.val) • ⊤ : Submodule L₀ L₀))
        (g₀ (N + 1))
      rw [hI]
      exact (isSMulRegular_map (Ideal.Quotient.mk (I₀ N)) (fun _ => rfl)).mp
        (deltaPDivisionFiniteStage_next_isSMulRegular D y hpA hg v hv hy N)

/-- 実δ関係g₀,…,g_NのKoszul複体は、実際の有限通常商の分解。
André・perfectoid化全射性の引用には依存しない。 -/
theorem deltaPDivisionFiniteRelations_isKoszulResolution
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (v : Aˣ) (hv : (v : A) = D.delta (p : A))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) (N : ℕ) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (N + 1) => g₀ i.val) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (deltaPDivisionFiniteRelations_isWeaklyRegular D y hpA hg v hv hy N)

end SerrePositivity.BhattScholze
