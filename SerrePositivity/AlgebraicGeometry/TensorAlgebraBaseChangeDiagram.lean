module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：KST §5、Stacks 0810・0811 の係数環の塔に沿う実際のテンソル代数の基底変更写像。
方針：左係数環の構造写像と右係数環の恒等写像のテンソル積を取り、両構造写像を照合する。
規約：右係数の代数作用を明示し、大域インスタンスにはしない。
使われ方：二段の追加基底変更を元の基礎環上の一段の表示へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable (A B C E : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
  [Algebra A B] [Algebra A C] [Algebra A E] [Algebra C E] [IsScalarTower A C E]

/--
概要：係数環の塔に沿うテンソル代数の実際の基底変更写像。
方針：左因子に構造写像、右因子に恒等写像を適用する。
規約：KST §5、Stacks 0810・0811、元の基礎環上の代数準同型として定める。
使われ方：押し出し図式の下辺となる実際の写像。
-/
def tensorAlgebraBaseChangeMap : (C ⊗[A] B) →ₐ[A] (E ⊗[A] B) :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A C E) (AlgHom.id A B)

/--
概要：テンソル代数の基底変更写像は左係数の像を保つ。
方針：純テンソルの公式を適用する。
規約：KST §5、Stacks 0810・0811、右係数は 1 とする。
使われ方：中間係数環の作用の塔を確認する。
-/
theorem tensorAlgebraBaseChangeMap_left (c : C) :
    tensorAlgebraBaseChangeMap A B C E (algebraMap C (C ⊗[A] B) c) =
      algebraMap E (E ⊗[A] B) (algebraMap C E c) := by
  simp [tensorAlgebraBaseChangeMap, Algebra.TensorProduct.algebraMap_apply]

/--
概要：テンソル代数の基底変更写像は右係数の像を保つ。
方針：左係数 1 の純テンソルの公式を使う。
規約：KST §5、Stacks 0810・0811、右因子の代数構造は局所的に指定する。
使われ方：元の代数からの加群の二段基底変更を取り消す。
-/
theorem tensorAlgebraBaseChangeMap_right (b : B) :
    tensorAlgebraBaseChangeMap A B C E ((1 : C) ⊗ₜ[A] b) = (1 : E) ⊗ₜ[A] b := by
  simp [tensorAlgebraBaseChangeMap]

/--
概要：中間係数環から新しいテンソル代数への二つの経路は作用の塔を与える。
方針：左係数の計算式を構造写像の合成等式にする。
規約：KST §5、Stacks 0810・0811、中間係数の作用は最終係数環を経由して定める。
使われ方：標準テンソル積が中間係数環上の押し出しとなることを証明する。
-/
theorem tensorAlgebraBaseChange_isScalarTower_left :
    let D := C ⊗[A] B
    let F := E ⊗[A] B
    letI : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
    letI : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
    IsScalarTower C D F := by
  let D := C ⊗[A] B
  let F := E ⊗[A] B
  let : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
  let : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  have hs (c : C) (x : F) : c • x = (algebraMap C E c) • x := by
    calc
      c • x = (c • (1 : E)) • x := by rw [smul_assoc, one_smul]
      _ = (algebraMap C E c) • x := by
        rw [show c • (1 : E) = algebraMap C E c by rw [Algebra.smul_def, mul_one]]
  refine ⟨fun c y x => ?_⟩
  change algebraMap D F (c • y) * x = c • (algebraMap D F y * x)
  rw [Algebra.smul_def, map_mul, hs, Algebra.smul_def]
  change tensorAlgebraBaseChangeMap A B C E (algebraMap C D c) *
      algebraMap D F y * x = _
  rw [tensorAlgebraBaseChangeMap_left, mul_assoc]

/--
概要：元の右係数代数から新しいテンソル代数への二つの経路は作用の塔を与える。
方針：右係数の純テンソルの公式で構造写像の合成を照合する。
規約：KST §5、Stacks 0810・0811、両テンソル代数の右因子の作用を明示する。
使われ方：押し出し後の加群の二段テンソルの取消。
-/
theorem tensorAlgebraBaseChange_isScalarTower_right :
    let D := C ⊗[A] B
    let F := E ⊗[A] B
    letI : Algebra B D := Algebra.TensorProduct.rightAlgebra
    letI : Algebra B F := Algebra.TensorProduct.rightAlgebra
    letI : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
    IsScalarTower B D F := by
  let D := C ⊗[A] B
  let F := E ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  let : Algebra B F := Algebra.TensorProduct.rightAlgebra
  let : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq' (R := B) (S := C ⊗[A] B) (A := E ⊗[A] B)
  ext b
  exact (tensorAlgebraBaseChangeMap_right A B C E b).symm

/--
概要：代数構造から読む中間係数環の作用でも、テンソル基底変更写像は作用の塔を与える。
方針：左係数の計算式を代数構造の三つのスカラー作用に対する合成等式へ移す。
規約：KST §5、Stacks 0810・0811、三つの代数構造の作用を型に明示する。
使われ方：押し出し述語が使う代数構造の作用とテンソル作用を区別して照合する。
-/
theorem tensorAlgebraBaseChange_isScalarTower_left_algebra :
    let D := C ⊗[A] B
    let F := E ⊗[A] B
    letI : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
    letI : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
    @IsScalarTower C D F (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D F).toSMul (inferInstance : Algebra C F).toSMul := by
  let D := C ⊗[A] B
  let F := E ⊗[A] B
  let : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
  let : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq' (R := C) (S := D) (A := F)
  ext c
  exact (tensorAlgebraBaseChangeMap_left A B C E c).symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
