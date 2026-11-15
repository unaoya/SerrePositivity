module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
概要：有限ファイバー冪の射影表示に使う、実際の Segre 座標の評価。
方針：二つの座標の組を対応する純テンソルへ送る多項式評価を使う。
規約：零環と空の添字を許し、平坦性や次数保存はここでは仮定しない。
使われ方：G3 の Segre 表示の核と標準開の比較の入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R A B ι κ : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B)

/-- 二つの次数一座標の積を純テンソルとして評価する実際の座標写像。 -/
def segreCoordinateMap : MvPolynomial (ι × κ) R →ₐ[R] (B ⊗[R] A) :=
  MvPolynomial.aeval (R := R) (fun ij ↦ b ij.2 ⊗ₜ[R] a ij.1)

@[simp]
theorem segreCoordinateMap_X (i : ι) (j : κ) :
    segreCoordinateMap a b (MvPolynomial.X (i, j)) = b j ⊗ₜ[R] a i := by
  simp [segreCoordinateMap]

@[simp]
theorem segreCoordinateMap_C (r : R) :
    segreCoordinateMap a b (MvPolynomial.C r) = algebraMap R (B ⊗[R] A) r := by
  simp [segreCoordinateMap]

end SerrePositivity.AlgebraicGeometry
