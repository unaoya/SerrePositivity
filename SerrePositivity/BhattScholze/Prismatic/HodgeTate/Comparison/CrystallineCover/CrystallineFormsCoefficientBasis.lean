module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# 結晶係数比較で使う通常形式の係数基底

## 概要
通常の多項式形式の係数拡大を、同じ単項式・外積の添字の基底で同定する。

## 方針
既存の polynomialFormsBasis の係数拡大と、同じ添字の終域基底を同定する。

## 規約
この同型の基底上の値を明示する。これだけで HT 写像との可換性を主張しない。

## 使われ方
特定の Zp 係数射における、元の形式の係数拡大の全単射性を計算する。
-/

public noncomputable section
universe u
open scoped TensorProduct
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
open SerrePositivity.DeRham
variable (k l T : Type u) [CommRing k] [CommRing l] [Algebra k l]
variable [Fintype T] [LinearOrder T]

/-- 同じ単項式と外積の添字を保つ、通常形式の係数拡大の線形同型。 -/
def crystallineFormsCoefficientBaseChangeEquiv (i : ℕ) :
    l ⊗[k] forms k T i ≃ₗ[l] forms l T i :=
  ((polynomialFormsBasis k T i).baseChange l).equiv
    (polynomialFormsBasis l T i) (Equiv.refl _)

/-- この係数同型は、元の単位純テンソルの基底を同じ終域基底へ送る。 -/
theorem crystallineFormsCoefficientBaseChangeEquiv_basis (i : ℕ)
    (v : (T →₀ ℕ) × Set.powersetCard T i) :
    crystallineFormsCoefficientBaseChangeEquiv k l T i
        ((1 : l) ⊗ₜ[k] polynomialFormsBasis k T i v) =
      polynomialFormsBasis l T i v := by
  simpa only [crystallineFormsCoefficientBaseChangeEquiv,
    Module.Basis.baseChange_apply, Equiv.refl_apply] using
    Module.Basis.equiv_apply ((polynomialFormsBasis k T i).baseChange l) v
      (polynomialFormsBasis l T i) (Equiv.refl _)

/-- 任意の終域係数を持つ純テンソルの基底上の値。 -/
theorem crystallineFormsCoefficientBaseChangeEquiv_tmul_basis (i : ℕ) (b : l)
    (v : (T →₀ ℕ) × Set.powersetCard T i) :
    crystallineFormsCoefficientBaseChangeEquiv k l T i
        (b ⊗ₜ[k] polynomialFormsBasis k T i v) = b • polynomialFormsBasis l T i v := by
  have hb : (b ⊗ₜ[k] polynomialFormsBasis k T i v) =
      b • ((1 : l) ⊗ₜ[k] polynomialFormsBasis k T i v) := by
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul' b (1 : l) (polynomialFormsBasis k T i v)).symm
  rw [hb, map_smul, crystallineFormsCoefficientBaseChangeEquiv_basis]

end SerrePositivity.BhattScholze.Prismatic.HTUniversalCrystallineInput
