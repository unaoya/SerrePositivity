module

public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangeDiagram
public import Mathlib.RingTheory.IsTensorProduct

/-!
概要：KST §5、Stacks 0810・0811 の係数環の塔に沿うテンソル代数の押し出し。
方針：二段テンソルの取消代数同型が右構造写像を保つことを確認する。
規約：実際の基底変更写像で定めた代数構造と作用の塔を使う。
使われ方：相対自由化基本開の保存を元の基礎環上の一段表示へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：取消代数同型は中間テンソル代数からの右構造写像を実際の係数変更写像へ送る。
方針：中間テンソル代数の純テンソルに還元し、取消同型と係数変更写像の公式を照合する。
規約：KST §5、Stacks 0810・0811、構造写像の環準同型としての等式。
使われ方：取消同型による移送後に中間代数上の加群のテンソルを取り消す。
-/
theorem tensorAlgebraBaseChange_cancel_includeRight
    (A B C E : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A E] [Algebra C E] [IsScalarTower A C E] :
    (Algebra.TensorProduct.cancelBaseChange A C E E B).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          (C ⊗[A] B) →ₐ[C] E ⊗[C] (C ⊗[A] B)).toRingHom =
      (tensorAlgebraBaseChangeMap A B C E).toRingHom := by
  apply RingHom.ext
  intro x
  change (Algebra.TensorProduct.cancelBaseChange A C E E B) ((1 : E) ⊗ₜ[C] x) =
    tensorAlgebraBaseChangeMap A B C E x
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    simp [tensorAlgebraBaseChangeMap, Algebra.smul_def]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/--
概要：係数環の塔に沿う一段表示のテンソル代数は、中間テンソル代数の実際の押し出しである。
方針：二段テンソルの取消代数同型を構成し、元の代数からの構造写像と可換であることを純テンソルで確認する。
規約：KST §5、Stacks 0810・0811、有限性や平坦性は不要。
使われ方：二段基底変更の保存結果を一段の標準テンソル積に接続する。
-/
theorem tensorAlgebraBaseChange_isPushout
    (A B C E : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing E]
    [Algebra A B] [Algebra A C] [Algebra A E] [Algebra C E] [IsScalarTower A C E] :
    let D := C ⊗[A] B
    let F := E ⊗[A] B
    letI : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
    letI : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
    letI : @IsScalarTower C E F (inferInstance : Algebra C E).toSMul
        (inferInstance : Algebra E F).toSMul (inferInstance : Algebra C F).toSMul :=
      IsScalarTower.of_algebraMap_eq' (R := C) (S := E) (A := F) rfl
    letI : @IsScalarTower C D F (inferInstance : Algebra C D).toSMul
        (inferInstance : Algebra D F).toSMul (inferInstance : Algebra C F).toSMul :=
      tensorAlgebraBaseChange_isScalarTower_left_algebra A B C E
    Algebra.IsPushout C E D F := by
  let D := C ⊗[A] B
  let F := E ⊗[A] B
  let : Algebra C F := ((algebraMap E F).comp (algebraMap C E)).toAlgebra
  let : Algebra D F := (tensorAlgebraBaseChangeMap A B C E).toRingHom.toAlgebra
  let : @IsScalarTower C E F (inferInstance : Algebra C E).toSMul
      (inferInstance : Algebra E F).toSMul (inferInstance : Algebra C F).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := E) (A := F) rfl
  let : @IsScalarTower C D F (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D F).toSMul (inferInstance : Algebra C F).toSMul :=
    tensorAlgebraBaseChange_isScalarTower_left_algebra A B C E
  let T := E ⊗[C] D
  let : Algebra D T := Algebra.TensorProduct.rightAlgebra
  let K : T ≃ₐ[E] F := Algebra.TensorProduct.cancelBaseChange A C E E B
  apply Algebra.IsPushout.of_equiv (R := C) (R' := E) (S := D) (S' := T) K
  exact tensorAlgebraBaseChange_cancel_includeRight A B C E

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
