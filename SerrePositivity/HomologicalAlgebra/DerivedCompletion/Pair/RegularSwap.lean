module
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Divisibility.Basic

public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# 正則対の順序交換

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u

/-! ## André E1・E2：ϖ の持上げの mod p 正則性（旧 Andre/Remark715/PerfectPrismVarpiRegular.lean）

## 概要

完全 prism (A,(d)) の商 R が p 正則なら、x=φ⁻¹(d) の mod p 像は正則。
BS 著者版 Remark 7.15（著者版 p.62）の p ねじれなしの場合の係数還元を具体化する。

## 方針

d の正則性と R の p 正則性から正則列の二元の順序を交換する。
mod p で x^p=d なので、正の冪から x 自身の正則性が従う。

## 規約

R の p 正則性を明示仮定とする。一般の perfectoid 基底へこの仮定を追加しない。

## 使われ方

原典の p ねじれなしの場合の中間計算を保持する。
実分冪降下の旧3宣言は不要になったため削除し、
Unconditional.VarpiPDReduction の射影的係数商による無条件版を使う。
置換先は原典と異なる線形切断による証明経路。
-/

@[expose] public noncomputable section PerfectPrismVarpiRegular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A]

/-- 概要：a が正則で、b が A/(a) で正則なら、a は A/(b) で正則。
方針：ac=be を mod a で調べ e=at とし、a を消去する。
規約：完備性や局所性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の d と p の順序交換。 -/
theorem principal_regular_swap (a b : A) (ha : IsSMulRegular A a)
    (hb : IsSMulRegular (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)) :
    IsSMulRegular (A ⧸ Ideal.span {b}) (Ideal.Quotient.mk (Ideal.span {b}) a) := by
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro c hc
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  change Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ c = 0 at hc
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hc
  obtain ⟨e, he⟩ := hc
  have he0 : Ideal.Quotient.mk (Ideal.span {a}) b * Ideal.Quotient.mk _ e = 0 := by
    rw [← map_mul, ← he, map_mul]
    simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a),
      zero_mul]
  have he' : Ideal.Quotient.mk (Ideal.span {a}) e = 0 :=
    hb (by simpa only [smul_eq_mul, mul_zero] using he0)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he')
  have hct : c = b * t := ha (by change a * c = a * (b * t); rw [he, ht]; ring)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr ⟨t, hct⟩

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiRegular

/-! ## André E1・E2：ϖ 還元した無限根入力環と原典の係数環（旧 Andre/Remark715/PerfectPrismVarpiRootInput.lean）

## 概要

完全 prism (A,(d)) で x=φ⁻¹(d)、ϖ=x mod d とする。
A/p 上の無限根環を x の係数像で割ると、R/ϖ 上の同じ無限根環と環同型。
BS 著者版 Remark 7.15（著者版 p.62）の入力台環を具体的な商から得る。

## 方針

無限根環と係数主イデアル商の交換同型に、(A/p)/(x) と R/ϖ の係数同型を合成する。
係数・根変数・通常多項式の評価を計算する。

## 規約

prism 商の p 正則性もモニック性も、この入力環の同型自体には不要。

## 使われ方

還元後の実 pd 包を原典の R/ϖ 上のモニック入力と比較するための台環同型。
-/

