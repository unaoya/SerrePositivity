module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteModPrimeTail
public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiRegular
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient

/-!
# André E1・E2：有限 mod p 関係商での次関係の正則性

## 概要

有限 δ 関係商の mod p で d が正則なら、次の δ 関係もそこで正則。
BS Rem 7.15（著者版 p.62）の p 正則性の同時帰納法への次段の入力。

## 方針

最高係数 φ^(N+1)(d) を d の正冪と計算し、有限変数分離後の一次式に適用する。

## 規約

d の正則性を保つ帰納法そのものは別工程。完備化の離散性をここでは結論しない。

## 使われ方

有限 raw 包の p 正則性を正則列の順序交換で保つ。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：正則な先頭係数を持つ一次多項式は正則。
方針：最高係数による多項式の非零因子判定を使う。
規約：係数環が零環の場合も含める。
使われ方：BS Rem 7.15（著者版 p.62）の次 δ 関係の線形表示。 -/
theorem linearPolynomial_regular {R : Type u} [CommRing R] (c b : R)
    (hc : IsSMulRegular R c) :
    IsSMulRegular (Polynomial R) (Polynomial.C c * Polynomial.X + Polynomial.C b) := by
  change Function.Injective (fun x : Polynomial R =>
    (Polynomial.C c * Polynomial.X + Polynomial.C b) * x)
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

/-- 概要：指定変数の正則係数一次式は多変数多項式環でも正則。
方針：指定変数を一変数として分離し、残りの変数の平坦性を使う。
規約：変数族は任意。
使われ方：BS Rem 7.15（著者版 p.62）の有限商後の次関係。 -/
theorem linearMvPolynomial_regular {R : Type u} [CommRing R] {τ : Type v}
    (c b : R) (s : τ) (hc : IsSMulRegular R c) :
    IsSMulRegular (MvPolynomial τ R) (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : τ // t ≠ s})
  have he : e (MvPolynomial.C c * MvPolynomial.X s + MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C c) * Polynomial.X + Polynomial.C (MvPolynomial.C b) := by
    simp [e, MvPolynomial.renameEquiv]
  have hc' := hc.of_flat (S := MvPolynomial {t : τ // t ≠ s} R)
  have hr := linearPolynomial_regular (MvPolynomial.C c) (MvPolynomial.C b) hc'
  intro x y h
  apply e.injective
  apply hr
  have hh := congrArg e h
  simpa only [smul_eq_mul, map_mul, he] using hh

/-- 概要：正則対 c,b の線形除算関係 cX-b を課しても c は正則。
方針：mod c で関係が -b になることを使い、正則対の順序交換を適用する。
規約：c は係数環で正則、b は mod c で正則とする。
使われ方：BS Rem 7.15（著者版 p.62）の最初の δ 関係商で d を保つ計算。 -/
theorem linearMvPolynomial_coefficient_regular_quotient
    {R : Type u} [CommRing R] {τ : Type v} (c b : R) (s : τ)
    (hc : IsSMulRegular R c)
    (hb : IsSMulRegular (R ⧸ Ideal.span {c}) (Ideal.Quotient.mk (Ideal.span {c}) b)) :
    IsSMulRegular (MvPolynomial τ R ⧸
      Ideal.span {MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b})
      (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b})
        (MvPolynomial.C c)) := by
  let T := MvPolynomial τ R
  let g : T := MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b
  let q := Ideal.Quotient.mk (Ideal.span {(MvPolynomial.C c : T)})
  have hcT : IsSMulRegular T (MvPolynomial.C c) := hc.of_flat (S := T)
  have hbT : IsSMulRegular (T ⧸ Ideal.span {(MvPolynomial.C c : T)})
      (q (MvPolynomial.C b)) :=
    SerrePositivity.isSMulRegular_mod_of_flat c b hc hb
  have hg : q g = -q (MvPolynomial.C b) := by
    change q (MvPolynomial.C c * MvPolynomial.X s - MvPolynomial.C b) = _
    rw [map_sub, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_mul, zero_sub]
  apply principal_regular_swap (MvPolynomial.C c : T) g hcT
  rw [hg]
  intro x y hxy
  apply hbT
  simpa only [neg_smul, neg_inj] using hxy

/-- 概要：p を殺す通常環射では反復 Frobenius は対応する p 冪。
方針：φ(r)=r^p+pδ(r) の像を帰納的に計算する。
規約：終域の δ 構造や非零性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の次関係の最高係数の正則性。 -/
theorem deltaFrobeniusIterate_map_of_prime_zero
    {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
    (D : DeltaStructure p A) (q : A →+* B) (hpq : q (p : A) = 0) (d : A) (n : ℕ) :
    q (D.frobeniusLift^[n] d) = q d ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', D.frobeniusLift_apply, map_add, map_pow,
      map_mul, hpq, zero_mul, add_zero, ih, ← pow_mul, Nat.pow_succ]

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B₀" => MvPolynomial (σ × Fin (N + 1)) A
local notation "J₀" => deltaDivisionFiniteStageInitialIdeal D d a N
local notation "Jp" => Ideal.span {(p : B₀)} ⊔ J₀
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I₀
local notation "e" => deltaDivisionFiniteModPrimeTailEquiv D d a N

/-- 概要：全自由環の有限 mod p 商での係数の正則性は初期係数商へ降りる。
方針：変数分離と係数多項式射の単射性を使う。
規約：元の A 係数 r を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の最高係数の冪の正則性。 -/
theorem deltaDivisionFiniteModPrimeInitial_coefficient_regular (r : A)
    (hr : IsSMulRegular (L₀ ⧸ Ip) (Ideal.Quotient.mk Ip (MvPolynomial.C r))) :
    IsSMulRegular (B₀ ⧸ Jp) (Ideal.Quotient.mk Jp (MvPolynomial.C r)) := by
  have hr' : IsSMulRegular (MvPolynomial (σ × ℕ) (B₀ ⧸ Jp))
      (MvPolynomial.C (σ := σ × ℕ) (Ideal.Quotient.mk Jp (MvPolynomial.C r))) := by
    intro x y hxy
    apply (e).symm.injective
    apply hr
    apply (e).injective
    simpa only [map_mul, smul_eq_mul, RingEquiv.apply_symm_apply,
      deltaDivisionFiniteModPrimeTailEquiv_coeff] using hxy
  intro x y hxy
  apply (MvPolynomial.C_injective (σ := σ × ℕ))
  apply hr'
  simpa only [smul_eq_mul, map_mul] using
    congrArg (MvPolynomial.C : (B₀ ⧸ Jp) →+* MvPolynomial (σ × ℕ) (B₀ ⧸ Jp)) hxy

/-- 概要：mod p の有限関係商で d が正則なら次の δ 関係も正則。
方針：初期商の先頭係数を d の正冪と同定し、後続変数の一次式へ適用する。
規約：帰納法の入力である d の mod p 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の有限 raw 関係商の p 正則性。 -/
theorem deltaDivisionFiniteModPrime_next_regular
    (hd : IsSMulRegular (L₀ ⧸ Ip) (Ideal.Quotient.mk Ip (MvPolynomial.C d))) (s : σ) :
    IsSMulRegular (L₀ ⧸ Ip)
      (Ideal.Quotient.mk Ip (deltaDivisionIteratedRelation D d a s (N + 1))) := by
  have hd' := deltaDivisionFiniteModPrimeInitial_coefficient_regular D d a N d hd
  let q : A →+* B₀ ⧸ Jp := (Ideal.Quotient.mk Jp).comp MvPolynomial.C
  have hpq : q (p : A) = 0 := by
    change Ideal.Quotient.mk Jp (MvPolynomial.C (p : A)) = 0
    rw [map_natCast]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {(p : B₀)} ≤ Jp from le_sup_left) (Ideal.mem_span_singleton_self _))
  have hc : IsSMulRegular (B₀ ⧸ Jp)
      (Ideal.Quotient.mk Jp (MvPolynomial.C (D.frobeniusLift^[N + 1] d))) := by
    change IsSMulRegular (B₀ ⧸ Jp) (q (D.frobeniusLift^[N + 1] d))
    rw [deltaFrobeniusIterate_map_of_prime_zero D q hpq]
    exact hd'.pow _
  have hreg := linearMvPolynomial_regular
    (Ideal.Quotient.mk Jp (MvPolynomial.C (D.frobeniusLift^[N + 1] d)))
    (Ideal.Quotient.mk Jp (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1))) (s, 0) hc
  intro x y hxy
  apply (e).injective
  apply hreg
  simpa only [smul_eq_mul, map_mul, deltaDivisionFiniteModPrimeTailEquiv_next] using congrArg e hxy

end SerrePositivity.BhattScholze.Andre
