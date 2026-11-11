module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
概要：基底変更代数を右因子の環写像で比較する。
方針：テンソル積の写像で代数構造を与え、二つの押し出しの合成から比較四角形を得る。
規約：比較する二つのテンソル積は同じ左因子を持つ。
使われ方：Stacks 0814 で étale な始域の局所模型をアフィン試験環へ引き戻す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

variable (R A B D : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R D] [Algebra B D] [IsScalarTower R B D]

/--
概要：右因子の環拡大に沿うテンソル積の間の自然な代数構造。
方針：左因子は恒等写像とし、右因子の環写像をテンソルする。
規約：右因子の環拡大は R 上で与える。
使われ方：始域の étale 写像のアフィン底変換を表す。
-/
@[instance_reducible]
def tensorRightBaseChangeAlgebra : Algebra (A ⊗[R] B) (A ⊗[R] D) :=
  (Algebra.TensorProduct.map (AlgHom.id R A) (IsScalarTower.toAlgHom R B D)).toAlgebra

/--
概要：テンソル積の右因子の比較写像は左因子のスカラーを保つ。
方針：左因子の包含を純テンソルで書く。
規約：テンソル積の代数構造は右因子の比較写像で指定する。
使われ方：始域の底変換を試験環の加群として扱う。
-/
theorem tensorRightBaseChange_isScalarTower_left :
    letI := tensorRightBaseChangeAlgebra R A B D
    IsScalarTower A (A ⊗[R] B) (A ⊗[R] D) := by
  let := tensorRightBaseChangeAlgebra R A B D
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change a ⊗ₜ[R] (1 : D) = Algebra.TensorProduct.map (AlgHom.id R A)
    (IsScalarTower.toAlgHom R B D) (a ⊗ₜ[R] (1 : B))
  simp

/--
概要：テンソル積の比較写像は、右因子の元の環の作用と両立する。
方針：右因子の包含を純テンソルで書く。
規約：右因子の拡大から合成して得る作用を使う。
使われ方：テンソル積の比較四角形の押し出しと加群の基底変更。
-/
theorem tensorRightBaseChange_isScalarTower_right :
    letI : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra D (A ⊗[R] D) := Algebra.TensorProduct.rightAlgebra
    letI := tensorRightBaseChangeAlgebra R A B D
    letI : Algebra B (A ⊗[R] D) := Algebra.compHom _ (algebraMap B D)
    IsScalarTower B (A ⊗[R] B) (A ⊗[R] D) := by
  let : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let : Algebra D (A ⊗[R] D) := Algebra.TensorProduct.rightAlgebra
  let := tensorRightBaseChangeAlgebra R A B D
  let : Algebra B (A ⊗[R] D) := Algebra.compHom _ (algebraMap B D)
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change (1 : A) ⊗ₜ[R] algebraMap B D b = Algebra.TensorProduct.map (AlgHom.id R A)
    (IsScalarTower.toAlgHom R B D) ((1 : A) ⊗ₜ[R] b)
  simp

/--
概要：右因子の比較写像で結んだ二つのテンソル積は、右因子に関する押し出しをなす。
方針：左側の四角形と外側の四角形はそれぞれテンソル積の押し出しなので、右側の四角形も押し出し。
規約：右因子の作用はテンソル積の右の包含で与える。
使われ方：始域の平坦性の保存と、二つの基底変更加群の比較。
-/
theorem tensorRightBaseChange_isPushout :
    letI : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra D (A ⊗[R] D) := Algebra.TensorProduct.rightAlgebra
    letI := tensorRightBaseChangeAlgebra R A B D
    letI : Algebra B (A ⊗[R] D) := Algebra.compHom _ (algebraMap B D)
    letI : IsScalarTower B D (A ⊗[R] D) := IsScalarTower.of_algebraMap_eq' rfl
    letI := tensorRightBaseChange_isScalarTower_right R A B D
    Algebra.IsPushout B (A ⊗[R] B) D (A ⊗[R] D) := by
  let E := A ⊗[R] B
  let F := A ⊗[R] D
  let : Algebra B E := Algebra.TensorProduct.rightAlgebra
  let : Algebra D F := Algebra.TensorProduct.rightAlgebra
  let : Algebra E F := tensorRightBaseChangeAlgebra R A B D
  let : Algebra B F := Algebra.compHom F (algebraMap B D)
  let : IsScalarTower A E F := tensorRightBaseChange_isScalarTower_left R A B D
  let : IsScalarTower B D F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B E F := tensorRightBaseChange_isScalarTower_right R A B D
  let : IsScalarTower R D F := Algebra.TensorProduct.right_isScalarTower
  let : IsScalarTower R B F := IsScalarTower.of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq R D F, IsScalarTower.algebraMap_eq R B D,
      ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq B D F]
  let : IsScalarTower R E F := .to₁₃₄ R A E F
  let : Algebra.IsPushout B D E F :=
    (Algebra.IsPushout.comp_iff R B A E).mp (inferInstance : Algebra.IsPushout R D A F)
  exact Algebra.IsPushout.symm inferInstance

end SerrePositivity.AlgebraicGeometry
