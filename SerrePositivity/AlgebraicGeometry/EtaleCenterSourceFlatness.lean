module

public import SerrePositivity.AlgebraicGeometry.EtaleCenterAffineTests
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr
public import SerrePositivity.AlgebraicGeometry.PureTransformScalarRestriction
public import SerrePositivity.AlgebraicGeometry.TensorRightBaseChange

/-!
概要：局所基底の中心で得た平坦性を、始域の底変換上の純変換に移す。
方針：基底と始域のテンソル積の比較四角形を押し出しにし、純変換のスカラーを比較する。
規約：局所基底への写像は平坦。
使われ方：Stacks 0814 で元の試験環上の有限被覆による平坦性の降下を行う。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所基底の純変換の平坦性は、底変換した局所始域の純変換の元の試験環上の平坦性を与える。
方針：二つの環のテンソル積を押し出しで比較し、平坦な局所基底から試験環へスカラーを制限する。
規約：局所始域の加群は始域環上で与える。
使われ方：共通中心の上で、各 étale 局所始域に対応する平坦性を得る。
-/
theorem HasFlatPurePullbacks.flat_source_affine_test
    {R A : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R) (j : Spec A ⟶ X)
    (C D : Type u) [CommRing C] [CommRing D] [Algebra R C] [Algebra R D] [Algebra C D]
    [IsScalarTower R C D] [Module.Flat R C]
    (a : R) (N : Type v) [AddCommGroup N] [Module C N] [Module D N] [IsScalarTower C D N]
    (h : HasFlatPurePullbacks
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R C))))
      (algebraMap R C a) N)
    (ha : IsRegular (pureTransformCoefficientMap p j a)) :
    letI : Algebra R A := (pureTransformCoefficientMap p j).toAlgebra
    let F := A ⊗[R] D
    letI : Algebra D F := Algebra.TensorProduct.rightAlgebra
    Module.Flat A (modulePureTransform (algebraMap A F (pureTransformCoefficientMap p j a))
      (F ⊗[D] N)) := by
  let φ := pureTransformCoefficientMap p j
  let : Algebra R A := φ.toAlgebra
  let E := A ⊗[R] C
  let F := A ⊗[R] D
  let : Algebra C E := Algebra.TensorProduct.rightAlgebra
  let : Algebra D F := Algebra.TensorProduct.rightAlgebra
  let : Algebra E F := tensorRightBaseChangeAlgebra R A C D
  let : Algebra C F := Algebra.compHom F (algebraMap C D)
  let : IsScalarTower C D F := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C E F := tensorRightBaseChange_isScalarTower_right R A C D
  let : IsScalarTower A E F := tensorRightBaseChange_isScalarTower_left R A C D
  let : Algebra.IsPushout C E D F := tensorRightBaseChange_isPushout R A C D
  let b := algebraMap A E (φ a)
  let P := F ⊗[D] N
  let e := Algebra.IsPushout.cancelBaseChange C E D F N
  let : Module.Flat E (modulePureTransform b (E ⊗[C] N)) :=
    h.flat_tensor_affine_test p j C a N ha
  let : Module.Flat E (modulePureTransform b P) :=
    Module.Flat.of_linearEquiv (modulePureTransformCongr b e)
  let : Module.Flat E (modulePureTransform (algebraMap E F b) P) :=
    (modulePureTransform_flat_iff_scalarRestriction (B := F) (M := P) b).mp inferInstance
  have hP := Module.Flat.trans A E (modulePureTransform (algebraMap E F b) P)
  change Module.Flat A (modulePureTransform (algebraMap A F (φ a)) P)
  rwa [IsScalarTower.algebraMap_apply A E F]

end SerrePositivity.AlgebraicGeometry
