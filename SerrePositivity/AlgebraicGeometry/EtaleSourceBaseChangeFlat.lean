module

public import SerrePositivity.AlgebraicGeometry.AffineSectionComponentLocus
public import SerrePositivity.AlgebraicGeometry.FlatSourceChange
public import SerrePositivity.AlgebraicGeometry.TensorAlgebraBaseChangeFlat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
概要：始域と基底を同時に étale 近傍へ移したときの相対平坦性。
方針：両方の写像から、通常の基底変換への étale な比較写像を作る。
規約：四角形の可換性はスカラー塔で表す。
使われ方：Stacks 0814・0815 で、局所有限化した部分に平坦化を適用する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：可換なアフィン四角形で基底と始域の水平写像が étale なら、元の基底上平坦な加群の引き戻しは新しい基底上平坦。
方針：基底変更への比較射は étale 射の合成からの消去で étale となる。基底変更と平坦な始域変更を順に適用する。
規約：四角形自体が Cartesian である必要はない。
使われ方：相対正規化の étale 局所モデルで境界外の平坦性を確認する。
-/
theorem flat_tensor_of_etale_source_base_change
    {R C B D M : Type u} [CommRing R] [CommRing C] [CommRing B] [CommRing D]
    [Algebra R C] [Algebra R B] [Algebra R D] [Algebra C D] [Algebra B D]
    [IsScalarTower R C D] [IsScalarTower R B D] [Algebra.Etale R C] [Algebra.Etale B D]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M] [Module.Flat R M] :
    Module.Flat C (D ⊗[B] M) := by
  let E := C ⊗[R] B
  let : Algebra B E := Algebra.TensorProduct.rightAlgebra
  let φ : E →ₐ[C] D :=
    Algebra.TensorProduct.lift (Algebra.ofId C D) (IsScalarTower.toAlgHom R B D) fun _ _ => .all _ _
  let : Algebra E D := φ.toRingHom.toAlgebra
  let : IsScalarTower C E D := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : IsScalarTower B E D := IsScalarTower.of_algebraMap_eq' <| by
    ext b
    change algebraMap B D b = φ (1 ⊗ₜ[R] b)
    rw [show φ (1 ⊗ₜ[R] b) = (Algebra.ofId C D) 1 * (IsScalarTower.toAlgHom R B D) b from
      Algebra.TensorProduct.lift_tmul _ _ _ _ _]
    rw [map_one, one_mul]
    rfl
  let g := Spec.map (CommRingCat.ofHom (algebraMap E D))
  let j := Spec.map (CommRingCat.ofHom (algebraMap B E))
  let e := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let : Etale e := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : Etale j := MorphismProperty.of_isPullback (isPullback_specTensor R B C).flip inferInstance
  have hg : g ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B D)) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq B E D).symm
  let : Etale (g ≫ j) := hg ▸ ((HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale B D)))
  let : Etale g := Etale.of_comp g j
  let : Algebra.Etale E D := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp (inferInstance : Etale g))
  let : Module.Flat C (E ⊗[B] M) :=
    Module.Flat.of_linearEquiv (tensorAlgebraBaseChangeEquiv R B C M)
  let : Module.Flat C (D ⊗[E] (E ⊗[B] M)) :=
    flat_tensor_of_flat_source_change
  let E₀ := TensorProduct.AlgebraTensorModule.cancelBaseChange B E D D M
  exact Module.Flat.of_linearEquiv (E₀.restrictScalars C).symm

end SerrePositivity.AlgebraicGeometry
