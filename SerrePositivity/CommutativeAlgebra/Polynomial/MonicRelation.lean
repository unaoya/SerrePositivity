module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Defs

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Polynomial.Expand
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.Tor

/-!
# 独立変数のモニック関係

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v w

/-! ## André E1：独立変数のモニック関係式（旧 Andre/MonicRelation.lean）

## 概要

任意のモニック多項式を多変数多項式環の指定変数で評価すると非零因子になる。
BS 著者版 Remark 7.15(1)（p.62）の pd 包の計算に必要な正則性の通常代数部分である。

## 方針

指定変数を一変数多項式として分離し、係数変更されたモニック多項式の正則性を移送する。
既存の冪根関係式の場合と同じ証明を任意のモニック多項式へ一般化する。

## 規約

係数環は任意で零環も許す。この正則性だけには正次数は不要である。
pd 包との比較や完備化後の忠実平坦性は主張しない。

## 使われ方

一元のモニック関係式と、独立変数の有限族を扱う際の最初の正則性入力に使う。
-/

@[expose] public noncomputable section MonicRelation

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：指定変数に課す通常の多項式関係式。
方針：係数を定数多項式へ写して評価する。
規約：δ 構造を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の一元関係の多変数版。 -/
def monicRelation {R : Type u} [CommRing R] {σ : Type v}
    (f : Polynomial R) (s : σ) : MvPolynomial σ R :=
  f.eval₂ MvPolynomial.C (MvPolynomial.X s)

/-- 概要：指定変数のモニック関係式は多変数多項式環で非零因子。
方針：指定変数の分離同型でモニックの一変数多項式に移す。
規約：正次数・素数・δ 構造を仮定しない。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の pd 包の正則性入力。 -/
theorem monicRelation_isSMulRegular {R : Type u} [CommRing R] {σ : Type v}
    (f : Polynomial R) (hf : f.Monic) (s : σ) :
    IsSMulRegular (MvPolynomial σ R) (monicRelation f s) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : σ // t ≠ s})
  have he : e (monicRelation f s) =
      f.map (MvPolynomial.C : R →+* MvPolynomial {t : σ // t ≠ s} R) := by
    change e.toRingHom (f.eval₂ MvPolynomial.C (MvPolynomial.X s)) = _
    rw [Polynomial.hom_eval₂]
    have hc : e.toRingHom.comp MvPolynomial.C =
        Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial {t : σ // t ≠ s} R) := by
      ext a
      simp [e, MvPolynomial.renameEquiv]
    rw [hc]
    have hx : e.toRingHom (MvPolynomial.X s) = Polynomial.X := by
      simp [e, MvPolynomial.renameEquiv]
    rw [hx]
    rfl
  have h := (hf.map (MvPolynomial.C : R →+* MvPolynomial {t : σ // t ≠ s} R)).isRegular.left
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

end SerrePositivity.BhattScholze.Andre

end MonicRelation

/-! ## B4-6：任意元族のモニック冪根添加環（旧 Andre/RootedExtension/MonicPowerFamilyCover.lean）

expand作用の自由加群を係数評価で基底変更し、指定した元のn乗根を持つ通常の環を作る。
この環のperfectoid性や完備性は結論しない。
-/

@[expose] public noncomputable section MonicPowerFamilyBaseQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- 既存係数商同型と標準商射の合成は係数の商写像である。 -/
theorem monicPowerFamilyCoefficientQuotient_comp (I : Ideal R) :
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom.comp
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))) =
      MvPolynomial.map (Ideal.Quotient.mk I) := by
  apply RingHom.ext
  intro x
  change MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk I)) MvPolynomial.X x = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

end SerrePositivity.BhattScholze

end MonicPowerFamilyBaseQuotient

/-! ## André E1：係数商後のモニック関係の正則性（旧 Andre/MonicRelationResidue.lean）

## 概要

任意の係数イデアルで割った後も、指定変数のモニック関係式は非零因子である。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の正則性入力を供給する。

## 方針

係数商と多項式環の交換同型で元の商を移し、モニック性の係数変更と変数分離を使う。
既存の冪根族のファイルから使うのは任意多項式上の係数射の恒等式だけである。

## 規約

係数環・係数イデアルは任意で、正次数や δ 構造を要求しない。
実導来還元の離散性や prismatic envelope の比較は別工程である。

## 使われ方

任意モニック f を入力する一元 raw δ p 除算の p 正則性の前提に用いる。
-/

