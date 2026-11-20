module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Flat.Basic

/-!
概要：KST §5、Stacks 0810 の代数と加群の基底変更の二つの表示の照合。
方針：テンソル代数の押し出しに対する加群の実際の取消同型を使う。
規約：右因子の代数作用を明示し、大域インスタンスにはしない。
使われ方：境界外の加群の平坦性を基底変更した自由表示の対象へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (R B C M : Type*) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M] [Module B M]
  [IsScalarTower R B M]

/--
概要：元の代数上の加群の二つの基底変更表示の実際の係数環線形同型。
方針：テンソル代数の押し出しに対する取消同型を適用する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、右因子の代数作用を明示する。
使われ方：係数環上の平坦性と元の自由表示の基底変更を照合する。
-/
def tensorAlgebraBaseChangeEquiv :
    letI : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    ((C ⊗[R] B) ⊗[B] M) ≃ₗ[C] (C ⊗[R] M) := by
  let : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  exact Algebra.IsPushout.cancelBaseChange R C B (C ⊗[R] B) M

/--
概要：二つの基底変更表示の同型は元の加群の像を保つ。
方針：押し出しの取消同型の純テンソルの公式を使う。
規約：KST §5、Stacks 0810、係数は単位元とする。
使われ方：基底変更した生成全射と元の加群からの射の両立性。
-/
theorem tensorAlgebraBaseChangeEquiv_one_tmul (m : M) :
    letI : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    tensorAlgebraBaseChangeEquiv R B C M ((1 : C ⊗[R] B) ⊗ₜ[B] m) =
      (1 : C) ⊗ₜ[R] m := by
  let : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  exact Algebra.IsPushout.cancelBaseChange_tmul R C B (C ⊗[R] B) M m

/--
概要：係数環上平坦な基底変更加群を、元の代数の表示を基底変更した対象としても平坦とみなせる。
方針：二つの基底変更表示の実同型で平坦性を運ぶ。
規約：KST §5、Stacks 0810、元の加群の基礎環上の平坦性は仮定しない。
使われ方：境界外だけで平坦な有限型加群の表示行列を扱う。
-/
theorem tensorAlgebraBaseChange_flat [Module.Flat C (C ⊗[R] M)] :
    letI : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    Module.Flat C ((C ⊗[R] B) ⊗[B] M) := by
  let : Algebra B (C ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  exact Module.Flat.of_linearEquiv (tensorAlgebraBaseChangeEquiv R B C M)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
