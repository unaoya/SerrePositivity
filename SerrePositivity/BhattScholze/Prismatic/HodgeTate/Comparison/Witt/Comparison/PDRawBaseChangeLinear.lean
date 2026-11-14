module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients

/-!
# 未完備の分冪模型のテンソル底変換

## 概要
小さい模型の各未完備項では、係数変更が通常のテンソル底変換を表す。

## 方針
多項式単項式と分冪単項式の基底を底変換し、係数射が同じ添字の基底を送ることを使う。

## 規約
任意の可換係数環の射を扱う。

## 使われ方
BS 著者版 Theorem 6.4 の完備底変換を計算するための未完備模型。
-/

public noncomputable section

open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r n : ℕ)

set_option maxRecDepth 1500 in
set_option backward.isDefEq.respectTransparency false in
/-- 小さい模型の未完備項は、任意の係数射によるテンソル底変換と両立する。 -/
theorem pdRawCoefficients_isBaseChange :
    IsBaseChange B (pdRawCoefficients A B r n).toLinearMap := by
  let b := pdRawBasis A r n
  let c := pdRawBasis B r n
  let e : B ⊗[A] pdRaw A r n ≃ₗ[B] pdRaw B r n :=
    (b.baseChange B).repr.trans c.repr.symm
  apply IsBaseChange.of_equiv e
  let f : pdRaw A r n →ₗ[A] pdRaw B r n :=
    (e.toLinearMap.restrictScalars A).comp (TensorProduct.mk A B (pdRaw A r n) 1)
  have hf : f = (pdRawCoefficients A B r n).toLinearMap := by
    apply b.ext
    intro i
    change e (1 ⊗ₜ[A] b i) = pdRawCoefficients A B r n (b i)
    rw [← Module.Basis.baseChange_apply]
    have h : e ((b.baseChange B) i) = c i := by
      change c.repr.symm ((b.baseChange B).repr ((b.baseChange B) i)) = c i
      rw [Module.Basis.repr_self, Module.Basis.repr_symm_single, one_smul]
    have hcoeff : pdRawCoefficients A B r n (b i) = c i :=
      pdRawCoefficients_basis A B r n i
    change e ((b.baseChange B) i) = pdRawCoefficients A B r n (b i)
    rw [h, hcoeff]
  intro x
  change f x = _
  exact DFunLike.congr_fun hf x

end SerrePositivity.BhattScholze.Prismatic
