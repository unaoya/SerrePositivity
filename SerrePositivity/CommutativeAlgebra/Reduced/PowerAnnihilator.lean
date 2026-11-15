module
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common

/-!
# 被約可換環の冪による消滅

概要：一般の構成とその比較をまとめる。
方針：元の型・本体・局所的な文脈を、機械的な名前の追従だけで保存する。
規約：特殊な包絡の存在や追加の仮定を導入しない。
使われ方：Bhatt–Scholze の包絡または perfectoid 化の比較。
-/

universe u

@[expose] public noncomputable section

/-- ## 概要
被約可換環で a の冪が x を消せば、a 自身が x を消す。
BS 著者版 Theorem 7.14（著者版 p.61）の極限段における一様ねじれ境界の補助命題。

## 方針
a*x の冪が零となることを掛け算の等式から示し、被約性を適用する。

## 規約
指数零と零環も許す。

## 使われ方
任意の p 冪ねじれに対し、共通指数 1 を与える。
-/
theorem _root_.SerrePositivity.CommutativeAlgebra.mul_eq_zero_of_pow_mul_eq_zero_of_reduced {S : Type u}
    [CommRing S] [IsReduced S] (a x : S) (n : ℕ)
    (hx : a ^ n * x = 0) : a * x = 0 := by
  cases n with
  | zero => simpa only [pow_zero, one_mul, mul_zero] using congrArg (a * ·) hx
  | succ n =>
    apply IsReduced.eq_zero _
    refine ⟨n+1, ?_⟩
    calc
      (a*x)^(n+1) = (a^(n+1)*x)*x^n := by ring
      _ = 0 := by rw [hx, zero_mul]



end
