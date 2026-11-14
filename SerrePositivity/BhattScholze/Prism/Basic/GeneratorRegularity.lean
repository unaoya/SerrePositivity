module
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Quotient
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Pair.RegularSwap

public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# 完全 prism の生成元の剰余正則性

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u

/-! ## ϖ の持上げの mod p 正則性

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

variable {p : ℕ} [Fact p.Prime]

/-- 概要：p 正則な prism 商を持つ完全 prism の生成元は mod p でも正則。
方針：prism 生成元の正則性と商の p 正則性の順序を交換する。
規約：仮定は R=A/(d) 上の p の単射性。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の ϖ の mod p 正則性への入力。 -/
theorem perfectPrism_generator_modPrime_regular (W : OrientedPrism p A)
    (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal)) :
    IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) W.generator) := by
  apply principal_regular_swap W.generator (p : A) W.generator_regular
  simpa only [OrientedPrism.ideal, map_natCast] using hpR

end SerrePositivity.BhattScholze.Andre

end PerfectPrismVarpiRegular

/-! ## ϖ 還元した無限根入力環と原典の係数環

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

