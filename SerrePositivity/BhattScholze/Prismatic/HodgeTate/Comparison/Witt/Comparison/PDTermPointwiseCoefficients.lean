module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermCompletedTensor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermCompletedTensor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseTensor

/-!
# 各項の完備係数拡大と小さい分冪模型

## 概要
加群の完備係数拡大関手の値を、実際の小さい分冪項に同定する。

## 方針
通常テンソルの完備化との線形比較に、分冪項の完備テンソル同型を合成する。

## 規約
環の係数変更を保持する。導来底変換との比較には別途離散性を使う。

## 使われ方
BS 著者版 Theorem 6.4、Witt 係数の交代余面複体を合わせるための各項の同型。
-/

public noncomputable section
open CategoryTheory
open scoped TensorProduct Simplicial ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l] (r n : ℕ)

/-- 各項の完備係数拡大は、係数変更後の小さい分冪項になる。 -/
def pdTermPointwiseCoefficientIso :
    (pCompletedScalarExtensionFunctor p (algebraMap k l)).obj
      (ModuleCat.of k (pdTerm p k r n)) ≅ ModuleCat.of l (pdTerm p l r n) :=
  pCompletedScalarExtensionTensorIso p k l (pdTerm p k r n) ≪≫
    (pdTermCompletedTensorAlgEquiv p k l r n).toLinearEquiv.toModuleIso

/-- 右脚の単位上で、線形比較は実際の模型の係数変更を与える。 -/
theorem pdTermPointwiseCoefficientIso_unit (x : pdTerm p k r n) :
    (pdTermPointwiseCoefficientIso p k l r n).hom
      (((moduleCompletionH0Unit l (p : l)).app
        ((ModuleCat.extendScalars (algebraMap k l)).obj (ModuleCat.of k (pdTerm p k r n))))
          ((1 : l) ⊗ₜ[k,algebraMap k l] x)) =
      pdTermCoefficientRingHom p k l r n x := by
  change pdTermCompletedTensorAlgEquiv p k l r n
    ((pCompletedScalarExtensionTensorIso p k l (pdTerm p k r n)).hom _) = _
  rw [pCompletedScalarExtensionTensorIso_unit, pdTermCompletedTensorAlgEquiv_coefficient]

end SerrePositivity.BhattScholze.Prismatic
