module

public import SerrePositivity.CommutativeAlgebra.WittCoefficientOne
public import Mathlib.RingTheory.WittVector.Teichmuller

/-! # Witt第1加法係数と整数係数の繰上り多項式

普遍整数多項式環のghost成分で計算し、任意の可換環へ評価する。
終域でpを約分しないため、pねじれを持つ環でも成立する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
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

end SerrePositivity
