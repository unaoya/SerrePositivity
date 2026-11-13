module

public import SerrePositivity.CommutativeAlgebra.DividedPowers.TruncatedPolynomialBasis
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FreeDPBasis
public import SerrePositivity.CommutativeAlgebra.DividedPowers.RankOneDP
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# 自由分冪代数の剰余ブロック

## 概要
p が零の係数環上で、自由分冪代数は切断多項式環上で自由（BS 著者版 Lemma 2.38）。

## 方針
各指数を p で割った商と剰余に分け、一元のブロック基底を座標ごとに掛ける。

## 規約
有限個の変数。零環も含む。

## 使われ方
正則列に沿う分冪包の mod p での Tor 計算。
-/

public noncomputable section

open scoped Classical

universe u v

namespace SerrePositivity.BhattScholze

variable {R : Type u} [CommRing R] {σ : Type v} [Fintype σ] {p : ℕ} [Fact p.Prime]

local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "P" => MvPolynomial σ R
local notation "I" => truncatedPolynomialIdeal R σ p
local notation "T" => P ⧸ I
local notation "D" => TruncatedMonomial σ p
local notation "γ[" s "," n "]" => DividedPowerAlgebra.dp R n (Finsupp.single s 1 : σ →₀ R)

omit [Fintype σ] [Fact p.Prime] in
private theorem freeDPGenerator_block (hp : (p : R) = 0) (s : σ) (k r : ℕ) :
    γ[s,1] ^ r * γ[s,p*k] = (r.factorial : G) * γ[s,p*k+r] := by
  let L : R →ₗ[R] (σ →₀ R) := LinearMap.toSpanSingleton R _ (Finsupp.single s 1)
  let f : DividedPowerAlgebra R R →ₐ[R] G := DividedPowerAlgebra.map R L
  have h := congrArg f (rankOneDPGenerator_pow_mul_prime_block hp k r)
  simpa only [map_mul, map_pow, map_natCast, f, DividedPowerAlgebra.map_apply_dp,
    L, LinearMap.toSpanSingleton_apply_one] using h

omit [Fintype σ] in
/-- 概要：一次分冪の p 乗は標数 p で零。
方針：一変数の恒等式を座標ごとの自由分冪代数への写像で移す。
規約：BS 著者版 Lemma 2.38 の剰余模型。
使われ方：切断多項式環からの標準射。 -/
theorem freeDPGenerator_pow_eq_zero (hp : (p : R) = 0) (s : σ) : γ[s,1] ^ p = 0 := by
  let L : R →ₗ[R] (σ →₀ R) := LinearMap.toSpanSingleton R _ (Finsupp.single s 1)
  let f : DividedPowerAlgebra R R →ₐ[R] G := DividedPowerAlgebra.map R L
  have h := congrArg f (rankOneDPGenerator_pow_eq_zero (Fact.out : p.Prime).pos hp)
  simpa only [map_pow, map_zero, f, DividedPowerAlgebra.map_apply_dp,
    L, LinearMap.toSpanSingleton_apply_one] using h

/-- 概要：切断多項式環から自由分冪代数への標準射。
方針：各変数を一次分冪に送り、その p 乗が零であることを使う。
規約：BS 著者版 Lemma 2.38 の mod p 表示。
使われ方：分冪代数の切断多項式環上の加群構造。 -/
@[expose] def freeDPTruncatedMap (hp : (p : R) = 0) : T →ₐ[R] G := by
  let f : P →ₐ[R] G := MvPolynomial.aeval (fun s : σ => γ[s,1])
  refine Ideal.Quotient.liftₐ I f ?_
  have hI : I ≤ RingHom.ker f.toRingHom := by
    unfold truncatedPolynomialIdeal
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change f ((MvPolynomial.X s : P)^p) = 0
    rw [map_pow, MvPolynomial.aeval_X]
    exact freeDPGenerator_pow_eq_zero hp s
  exact fun _ h => hI h

omit [Fintype σ] in
/-- 概要：切断商の代表元を一次分冪で評価する。
方針：切断イデアルからの商写像の計算式を使う。
規約：BS 著者版 Lemma 2.38 の mod p 表示。
使われ方：表示関係の Koszul 複体の平坦底変換。 -/
theorem freeDPTruncatedMap_mk (hp : (p : R) = 0) (f : P) :
    freeDPTruncatedMap hp (Ideal.Quotient.mk I f) =
      MvPolynomial.aeval (fun s : σ => γ[s,1]) f := rfl

/-- 概要：切断多項式の作用を標準射で与える。
方針：一次分冪への標準射の代数構造。
規約：BS 著者版 Lemma 2.38。
使われ方：分冪ブロック基底。 -/
abbrev freeDPTruncatedAlgebra (hp : (p : R) = 0) : Algebra T G :=
  (freeDPTruncatedMap (σ := σ) hp).toRingHom.toAlgebra

local instance [hp : Fact ((p : R) = 0)] : Algebra T G := freeDPTruncatedAlgebra hp.out

local instance [hp : Fact ((p : R) = 0)] : IsScalarTower R T G :=
  IsScalarTower.of_algebraMap_eq fun r => ((freeDPTruncatedMap (σ := σ) hp.out).commutes r).symm

private def blockIndexEquiv (hpos : 0 < p) : (σ →₀ ℕ) ≃ ((σ → ℕ) × D) where
  toFun m := (fun s => m s / p,
    ⟨Finsupp.equivFunOnFinite.symm (fun s => m s % p), fun s => Nat.mod_lt _ hpos⟩)
  invFun q := Finsupp.equivFunOnFinite.symm (fun s => p * q.1 s + q.2.val s)
  left_inv m := by
    ext s
    exact Nat.div_add_mod (m s) p
  right_inv q := by
    apply Prod.ext
    · funext s
      change (p * q.1 s + q.2.val s) / p = q.1 s
      rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt (q.2.property s), add_zero]
    · apply Subtype.ext
      ext s
      change (p * q.1 s + q.2.val s) % p = q.2.val s
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (q.2.property s)]

private def blockBasis (hp : (p : R) = 0) : Module.Basis ((σ → ℕ) × D) R G :=
  ((freeDPBasis σ R).reindex (blockIndexEquiv (Fact.out : p.Prime).pos)).isUnitSMul
    (w := fun q => ∏ s, ((q.2.val s).factorial : R))
    (fun q => IsUnit.prod_iff.mpr fun s _ =>
      rankOneDPPrimeBlock_factorial_isUnit (Fact.out : p.Prime) hp (q.2.property s))

private def highMonomial (k : σ → ℕ) : G :=
  freeDPMonomial σ R (Finsupp.equivFunOnFinite.symm fun s => p * k s)

private theorem blockBasis_apply [Fact ((p : R) = 0)] (k : σ → ℕ) (r : D) :
    blockBasis (Fact.out : (p : R) = 0) (k,r) =
      truncatedPolynomialBasis R σ p r • highMonomial (p := p) k := by
  rw [blockBasis, Module.Basis.isUnitSMul_apply, Module.Basis.reindex_apply, freeDPBasis_apply,
    truncatedPolynomialBasis_apply]
  change (∏ s, ((r.val s).factorial : R)) • _ =
    freeDPTruncatedMap (Fact.out : (p : R) = 0)
      (Ideal.Quotient.mk I (MvPolynomial.monomial r.val 1)) * highMonomial (p := p) k
  rw [Algebra.smul_def, map_prod]
  have hF : freeDPTruncatedMap (Fact.out : (p : R) = 0)
      (Ideal.Quotient.mk I (MvPolynomial.monomial r.val 1)) =
      ∏ s, γ[s,1] ^ r.val s := by
    change MvPolynomial.aeval (fun s : σ => γ[s,1]) (MvPolynomial.monomial r.val 1) = _
    rw [← MvPolynomial.prod_X_pow_eq_monomial, map_prod]
    simp only [map_pow, MvPolynomial.aeval_X]
    exact Finsupp.prod_fintype r.val (fun s n => γ[s,1] ^ n) (fun _ => pow_zero _)
  rw [hF, highMonomial]
  unfold freeDPMonomial
  simp_rw [Finsupp.prod_fintype _ (fun s n => γ[s,n])
    (fun s => DividedPowerAlgebra.dp_zero (R := R) (m := Finsupp.single s 1))]
  simp only [map_natCast]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  exact (freeDPGenerator_block (Fact.out : (p : R) = 0) s (k s) (r.val s)).symm

/-- 概要：p が零なら、自由分冪代数は切断多項式環上で自由。
方針：ブロックごとの最高指数の倍数部分を固定し、低指数単項式を作用させる。
規約：有限個の変数（BS 著者版 Lemma 2.38）。
使われ方：正則列の分冪包の mod p の Tor 計算。 -/
theorem freeDPTruncated_moduleFree (hp : (p : R) = 0) :
    letI := freeDPTruncatedAlgebra (σ := σ) hp
    Module.Free T G := by
  letI : Fact ((p : R) = 0) := ⟨hp⟩
  let f : ((σ → ℕ) →₀ T) →ₗ[T] G := Finsupp.linearCombination T (highMonomial (p := p))
  let b := Finsupp.basis (R := R) (fun _ : σ → ℕ => truncatedPolynomialBasis R σ p)
  let c := (blockBasis hp).reindex (Equiv.sigmaEquivProd (σ → ℕ) D).symm
  have hf : f.restrictScalars R = c.repr.symm.toLinearMap.comp b.repr.toLinearMap := by
    apply b.ext
    rintro ⟨k,r⟩
    change f (b ⟨k, r⟩) = c.repr.symm (b.repr (b ⟨k, r⟩))
    rw [Module.Basis.repr_self, Module.Basis.repr_symm_single_one]
    have hb : b ⟨k, r⟩ = Finsupp.single k (truncatedPolynomialBasis R σ p r) := by
      simp [b]
    have hc : c ⟨k, r⟩ = blockBasis hp (k, r) := by
      simp [c, Module.Basis.reindex_apply]
    rw [hb, hc]
    change Finsupp.linearCombination T _ (Finsupp.single k _) = _
    rw [Finsupp.linearCombination_single]
    exact (blockBasis_apply (R := R) (p := p) k r).symm
  have hbij : Function.Bijective f := by
    change Function.Bijective (f.restrictScalars R)
    rw [hf]
    exact (b.repr.trans c.repr.symm).bijective
  exact Module.Free.of_basis ((Finsupp.basisSingleOne (R := T) (ι := σ → ℕ)).map
    (LinearEquiv.ofBijective f hbij))

end SerrePositivity.BhattScholze
