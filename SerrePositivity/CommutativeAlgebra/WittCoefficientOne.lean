module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.Tactic.LinearCombination

/-! # Witt ベクトルの第一積係数

整数係数の普遍多項式環上で第一 ghost 成分の乗法性を使い、一般可換環へ評価する。
標数の仮定や perfectoid 性は必要ない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
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

end SerrePositivity
