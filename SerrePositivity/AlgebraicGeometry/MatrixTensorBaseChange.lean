module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の有限行列の写像とテンソル基底変更。
方針：有限自由加群とそのテンソル積の標準同型の下で係数変更行列の可換式を示す。
規約：基底変更の平坦性は仮定しない。
使われ方：小行列式の基底変更と実際の関係式の完全性を接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R C m n : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/--
概要：有限行列のテンソル基底変更は、標準的な自由加群の同型の下で係数変更行列の写像に一致する。
方針：純テンソルの各係数で行列の有限和と係数写像を計算する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、任意の係数環への基底変更。
使われ方：基底変更先の表示行列が正しい核を与えることの証明。
-/
theorem matrixTensorBaseChange_square (H : Matrix m n R) :
    (TensorProduct.piScalarRight R C C m).toLinearMap.comp (H.mulVecLin.baseChange C) =
      (H.map (algebraMap R C)).mulVecLin.comp
        (TensorProduct.piScalarRight R C C n).toLinearMap := by
  ext j i
  simp [TensorProduct.piScalarRightHom_tmul, Matrix.mulVec, dotProduct,
    Algebra.smul_def, Pi.single_apply]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
