module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.WittVector.Teichmuller

/-! # Witt ベクトルの ghost 写像と第 1 係数

## 概要

- `p` 倍が単射な可換環 `A` では、Witt ベクトルの ghost 写像は単射
  （`witt_ghostMap_injective_of_mul_prime_injective`）。Mathlib にあるのは `p` が可逆な場合だけ。
- 第 1 係数の公式：積は `(xy)_1 = x_0^p y_1 + x_1 y_0^p + p x_1 y_1`（`witt_mul_coeff_one`）、
  和は `(x+y)_1 = x_1 + y_1 + c(x_0, y_0)`（`witt_add_coeff_one`、`witt_add_coeff_one_eq_eval_carry`）。
  ここで繰上り多項式 `c = ([X_0] + [X_1])_1`（`wittAdditionCarry`、`[·]` は Teichmüller 元）は整数係数で、
  `p c = X_0^p + X_1^p - (X_0 + X_1)^p`（`p_mul_wittAdditionCarry`）。

## 方針

ghost 写像の単射性は、ghost 成分の漸化式で係数を帰納的に決め、`p^n` 倍の単射性で約す。
第 1 係数の公式は、整数係数の普遍多項式環（`p` ねじれがない）で第 1 ghost 成分を計算し、
任意の可換環へ評価して得る。終域で `p` を約分しないので、`p` ねじれを持つ環でも成り立つ。

## 規約

標数の仮定や perfectoid 性は置かない。Mathlib への提出候補（mathlib-upstream の G7）。

## 使われ方

δ 環の基本（BhattScholze の `DeltaRing`）、perfectoid 環の判定（`PerfectoidCharacteristicP`、
`PerfectoidFrobeniusCriterion`）、distinguished な関係式の計算（`WittDistinguishedTorsion`）、
André の補題の各所（BhattScholze）。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity

section GhostInjective

/-- Only injectivity of multiplication by p is needed for the Witt ghost map to be injective. -/
theorem witt_ghostMap_injective_of_mul_prime_injective
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    Function.Injective (WittVector.ghostMap (p := p) (R := A)) := by
  intro x y hxy
  apply WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrFun hxy n
    simp only [WittVector.ghostMap_apply, WittVector.ghostComponent_apply,
      aeval_wittPolynomial, Finset.sum_range_succ,
      Nat.sub_self, pow_zero, pow_one] at hn
    have hs : (∑ i ∈ Finset.range n, (p : A) ^ i * x.coeff i ^ p ^ (n - i)) =
        ∑ i ∈ Finset.range n, (p : A) ^ i * y.coeff i ^ p ^ (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih i (Finset.mem_range.mp hi)]
    rw [hs] at hn
    have hreg : IsSMulRegular A (p : A) := hp
    exact (hreg.pow n) (add_left_cancel hn)

end GhostInjective

section CoefficientOne

open MvPolynomial

/-- Witt ベクトルの第一 ghost 成分。 -/
theorem witt_ghostComponent_one (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] (x : WittVector p R) :
    WittVector.ghostComponent 1 x = (p : R) * x.coeff 1 + x.coeff 0 ^ p := by
  simp [WittVector.ghostComponent_apply, wittPolynomial_one]

/-- Witt ベクトルの第一積係数の普遍公式。 -/
theorem witt_mul_coeff_one (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] (x y : WittVector p R) :
    (x * y).coeff 1 = x.coeff 0 ^ p * y.coeff 1 + x.coeff 1 * y.coeff 0 ^ p +
      (p : R) * x.coeff 1 * y.coeff 1 := by
  let U := MvPolynomial (Fin 2 × ℕ) ℤ
  let a : WittVector p U := WittVector.mk p fun n => X (0, n)
  let b : WittVector p U := WittVector.mk p fun n => X (1, n)
  have hu := (WittVector.ghostComponent 1).map_mul a b
  rw [witt_ghostComponent_one, witt_ghostComponent_one, witt_ghostComponent_one,
    WittVector.mul_coeff_zero, mul_pow] at hu
  have he : (a * b).coeff 1 = a.coeff 0 ^ p * b.coeff 1 + a.coeff 1 * b.coeff 0 ^ p +
      (p : U) * a.coeff 1 * b.coeff 1 := by
    apply mul_left_cancel₀ (show (p : U) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    linear_combination hu
  let f : U →+* R := eval₂Hom (Int.castRingHom R) (fun z =>
    if z.1 = 0 then x.coeff z.2 else y.coeff z.2)
  have hfa : WittVector.map f a = x := by
    ext n
    change (X (0, n) : U).eval₂ (Int.castRingHom R)
      (fun z => if z.1 = 0 then x.coeff z.2 else y.coeff z.2) = x.coeff n
    rw [eval₂_X]
    simp
  have hfb : WittVector.map f b = y := by
    ext n
    change (X (1, n) : U).eval₂ (Int.castRingHom R)
      (fun z => if z.1 = 0 then x.coeff z.2 else y.coeff z.2) = y.coeff n
    rw [eval₂_X]
    simp
  have hf := congrArg f he
  simpa only [← WittVector.map_coeff, map_mul, map_add, map_pow, map_natCast,
    hfa, hfb] using hf

end CoefficientOne

section AdditionCarry

open MvPolynomial

/-- Witt第1加法係数は、各第1係数とTeichmüller和の繰上りの和。 -/
theorem witt_add_coeff_one (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] (x y : WittVector p R) :
    (x + y).coeff 1 = x.coeff 1 + y.coeff 1 +
      (WittVector.teichmuller p (x.coeff 0) +
        WittVector.teichmuller p (y.coeff 0)).coeff 1 := by
  let U := MvPolynomial (Fin 2 × ℕ) ℤ
  let a : WittVector p U := WittVector.mk p fun n ↦ X (0, n)
  let b : WittVector p U := WittVector.mk p fun n ↦ X (1, n)
  let c := WittVector.teichmuller p (a.coeff 0)
  let d := WittVector.teichmuller p (b.coeff 0)
  have hu := (WittVector.ghostComponent 1).map_add a b
  have ht := (WittVector.ghostComponent 1).map_add c d
  simp only [witt_ghostComponent_one, WittVector.add_coeff_zero] at hu ht
  simp only [c, d, WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_pos p _ 1 (by omega), mul_zero, zero_add] at ht
  have he : (a + b).coeff 1 = a.coeff 1 + b.coeff 1 + (c + d).coeff 1 := by
    apply mul_left_cancel₀ (show (p : U) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    linear_combination hu - ht
  let f : U →+* R := eval₂Hom (Int.castRingHom R)
    (fun z ↦ if z.1 = 0 then x.coeff z.2 else y.coeff z.2)
  have hfa : WittVector.map f a = x := by
    ext n
    change (X (0, n) : U).eval₂ (Int.castRingHom R)
      (fun z ↦ if z.1 = 0 then x.coeff z.2 else y.coeff z.2) = x.coeff n
    simp
  have hfb : WittVector.map f b = y := by
    ext n
    change (X (1, n) : U).eval₂ (Int.castRingHom R)
      (fun z ↦ if z.1 = 0 then x.coeff z.2 else y.coeff z.2) = y.coeff n
    simp
  have hf := congrArg f he
  simpa only [c, d, ← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
    hfa, hfb] using hf

/-- 整数係数の繰上り多項式。pで除した式を環内の除算としては定義しない。 -/
def wittAdditionCarry (p : ℕ) [Fact p.Prime] : MvPolynomial (Fin 2) ℤ :=
  (WittVector.teichmuller p (X 0 : MvPolynomial (Fin 2) ℤ) +
    WittVector.teichmuller p (X 1)).coeff 1

/-- p倍するとX^p+Y^p-(X+Y)^pとなる、整数多項式としての繰上り公式。 -/
theorem p_mul_wittAdditionCarry (p : ℕ) [Fact p.Prime] :
    (p : MvPolynomial (Fin 2) ℤ) * wittAdditionCarry p =
      X 0 ^ p + X 1 ^ p - (X 0 + X 1) ^ p := by
  have h := (WittVector.ghostComponent 1).map_add
    (WittVector.teichmuller p (X 0 : MvPolynomial (Fin 2) ℤ))
    (WittVector.teichmuller p (X 1))
  simp only [witt_ghostComponent_one, WittVector.add_coeff_zero,
    WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_pos p _ 1 (by omega),
    mul_zero, zero_add] at h
  change (p : MvPolynomial (Fin 2) ℤ) * wittAdditionCarry p + (X 0 + X 1) ^ p =
    X 0 ^ p + X 1 ^ p at h
  exact eq_sub_of_add_eq h

/-- 任意の可換環への繰上り多項式の評価は、Teichmüller和の第1係数。 -/
theorem eval_wittAdditionCarry (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] (x y : R) :
    eval₂ (Int.castRingHom R) (fun i : Fin 2 ↦ if i = 0 then x else y)
      (wittAdditionCarry p) =
      (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
  let f : MvPolynomial (Fin 2) ℤ →+* R :=
    eval₂Hom (Int.castRingHom R) (fun i ↦ if i = 0 then x else y)
  change f (wittAdditionCarry p) = _
  simp [wittAdditionCarry, ← WittVector.map_coeff, WittVector.map_teichmuller, f]

/-- Witt加法の第1係数を、整数係数の繰上り多項式の評価で表示する。 -/
theorem witt_add_coeff_one_eq_eval_carry (p : ℕ) [Fact p.Prime]
    {R : Type u} [CommRing R] (x y : WittVector p R) :
    (x + y).coeff 1 = x.coeff 1 + y.coeff 1 +
      eval₂ (Int.castRingHom R)
        (fun i : Fin 2 ↦ if i = 0 then x.coeff 0 else y.coeff 0) (wittAdditionCarry p) := by
  rw [eval_wittAdditionCarry, witt_add_coeff_one]

end AdditionCarry

end SerrePositivity
