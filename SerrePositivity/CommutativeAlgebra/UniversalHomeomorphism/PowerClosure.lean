module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.Ideal.Operations

/-!
# p 冪による部分環の閉包

## 概要
ある p 冪が部分環に属する元の全体と、部分環の導手を定義する。

## 方針
指数をそろえて環演算の閉性を示す。p 乗根で閉じた部分環の導手は根基イデアルになる。

## 規約
指数は元ごとに取り、一様な指数を仮定しない。

## 使われ方
普遍同相の標数 p における判定のための補助。
-/

@[expose] public section

namespace SerrePositivity.CommutativeAlgebra

variable {B : Type*} [CommRing B] (p : ℕ) [ExpChar B p]

/-- ある p 冪が `S` に属する元の部分環。 -/
def pPowerClosure (S : Subring B) : Subring B where
  carrier := {x | ∃ n : ℕ, x ^ (p ^ n) ∈ S}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [add_pow_expChar_pow]
    apply S.add_mem
    · rw [pow_add, pow_mul]
      exact S.pow_mem hn _
    · rw [Nat.add_comm n m, pow_add, pow_mul]
      exact S.pow_mem hm _
  mul_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [mul_pow]
    apply S.mul_mem
    · rw [pow_add, pow_mul]
      exact S.pow_mem hn _
    · rw [Nat.add_comm n m, pow_add, pow_mul]
      exact S.pow_mem hm _
  neg_mem' := by
    rintro x ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← iterateFrobenius_def, map_neg, iterateFrobenius_def]
    exact S.neg_mem hn

@[simp] theorem mem_pPowerClosure (S : Subring B) (x : B) :
    x ∈ pPowerClosure p S ↔ ∃ n : ℕ, x ^ (p ^ n) ∈ S := Iff.rfl

theorem le_pPowerClosure (S : Subring B) : S ≤ pPowerClosure p S :=
  fun x hx ↦ ⟨0, by simpa using hx⟩

/-- p 冪閉包は p 乗根で閉じている。 -/
theorem pow_mem_pPowerClosure_iff (S : Subring B) (x : B) :
    x ^ p ∈ pPowerClosure p S ↔ x ∈ pPowerClosure p S := by
  refine ⟨?_, fun hx ↦ (pPowerClosure p S).pow_mem hx p⟩
  rintro ⟨n, hn⟩
  exact ⟨n + 1, by simpa only [pow_succ', pow_mul] using hn⟩

/-- 部分環に含まれる最大の周囲の環のイデアル。 -/
def subringConductor (S : Subring B) : Ideal B where
  carrier := {x | ∀ y : B, x * y ∈ S}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy z
    simpa only [add_mul] using S.add_mem (hx z) (hy z)
  smul_mem' := by
    intro a x hx y
    change a * x * y ∈ S
    rw [mul_comm a x, mul_assoc]
    exact hx (a * y)

theorem subringConductor_le (S : Subring B) : (subringConductor S : Set B) ⊆ S :=
  fun x hx ↦ by simpa using hx 1

omit [ExpChar B p] in
/-- p 乗根で閉じた部分環の導手には冪零の厚みがない。 -/
theorem subringConductor_isRadical (S : Subring B) (hp : 1 < p)
    (hS : ∀ x : B, x ^ p ∈ S → x ∈ S) : (subringConductor S).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt p hp).mpr
  intro x hx y
  apply hS
  rw [mul_pow]
  exact hx (y ^ p)

end SerrePositivity.CommutativeAlgebra
