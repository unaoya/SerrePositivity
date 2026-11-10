module

public import SerrePositivity.AlgebraicGeometry.AffineSectionComponentLocus
public import SerrePositivity.AlgebraicGeometry.PureFreeStalkBaseChange
public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks

/-!
概要：局所基底への引き戻し上の平坦性を、元の基底のアフィン試験対象のテンソル積で調べる。
方針：試験射と局所基底の引き戻しをテンソル積で表し、境界の正則性を平坦性で保つ。
規約：局所基底への係数変更は平坦とする。
使われ方：Stacks 0814 の共通中心上で、局所始域から平坦性を降下する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所基底へ引き戻した中心上で純変換が平坦なら、元の基底上のアフィン試験対象を局所基底へ拡大しても平坦。
方針：テンソル積の Spec からスキームの引き戻しへの射を作り、係数写像を照合する。
規約：試験環で境界元が正則で、局所基底は平坦。
使われ方：共通中心の各試験環で、étale 始域の局所純変換を比較する。
-/
theorem HasFlatPurePullbacks.flat_tensor_affine_test
    {R A : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R) (j : Spec A ⟶ X)
    (C : Type u) [CommRing C] [Algebra R C] [Module.Flat R C]
    (a : R) (N : Type v) [AddCommGroup N] [Module C N]
    (h : HasFlatPurePullbacks
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R C))))
      (algebraMap R C a) N)
    (ha : IsRegular (pureTransformCoefficientMap p j a)) :
    letI : Algebra R A := (pureTransformCoefficientMap p j).toAlgebra
    let E := A ⊗[R] C
    letI : Algebra C E := Algebra.TensorProduct.rightAlgebra
    Module.Flat E (modulePureTransform (algebraMap A E (pureTransformCoefficientMap p j a))
      (E ⊗[C] N)) := by
  let φ := pureTransformCoefficientMap p j
  let : Algebra R A := φ.toAlgebra
  let E := A ⊗[R] C
  let : Algebra C E := Algebra.TensorProduct.rightAlgebra
  let f := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let g := Spec.map (CommRingCat.ofHom (algebraMap A E))
  let k := Spec.map (CommRingCat.ofHom (algebraMap C E))
  have hφ : Spec.map (CommRingCat.ofHom φ) = j ≫ p := Spec.map_preimage (j ≫ p)
  have hs : (g ≫ j) ≫ p = k ≫ f := by
    rw [Category.assoc, ← hφ]
    exact (isPullback_specTensor R C A).w.symm
  let t := pullback.lift (g ≫ j) k hs
  have ht : pureTransformCoefficientMap (pullback.snd p f) t = algebraMap C E := by
    unfold pureTransformCoefficientMap
    rw [pullback.lift_snd, show k = Spec.map (CommRingCat.ofHom (algebraMap C E)) from rfl,
      Spec.preimage_map]
    rfl
  let P (ψ : C →+* E) : Prop :=
    letI : Algebra C E := ψ.toAlgebra
    IsRegular (ψ (algebraMap R C a)) →
      Module.Flat E (modulePureTransform (ψ (algebraMap R C a)) (E ⊗[C] N))
  have hP : P (algebraMap C E) := (congrArg P ht).mp (h (.of E) t)
  change Module.Flat E (modulePureTransform (algebraMap A E (φ a)) (E ⊗[C] N))
  rw [show algebraMap A E (φ a) = algebraMap C E (algebraMap R C a) by
    change algebraMap A E (algebraMap R A a) = algebraMap C E (algebraMap R C a)
    rw [← IsScalarTower.algebraMap_apply R A E, ← IsScalarTower.algebraMap_apply R C E]]
  have hreg : IsRegular (algebraMap C E (algebraMap R C a)) := by
    rw [← IsScalarTower.algebraMap_apply R C E, IsScalarTower.algebraMap_apply R A E]
    exact algebraMap_isRegular_of_flat A E (φ a) ha
  unfold P at hP
  rw [toAlgebra_algebraMap] at hP
  exact hP hreg

end SerrePositivity.AlgebraicGeometry
