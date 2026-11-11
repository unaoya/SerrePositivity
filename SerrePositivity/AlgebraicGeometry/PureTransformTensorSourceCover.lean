module

public import SerrePositivity.AlgebraicGeometry.PureTransformAffineSourceDescent
public import SerrePositivity.AlgebraicGeometry.PureTransformCongr
public import SerrePositivity.AlgebraicGeometry.TensorRightBaseChange
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.FiniteStability

/-!
概要：試験環に底変換した有限アフィン始域被覆で、純変換の平坦性を降下する。
方針：始域被覆の各項のテンソル積を実際のアフィン引き戻しとして扱い、二段テンソルを比較する。
規約：始域被覆の各環写像は平坦で、有限個の像が始域の全点を覆う。
使われ方：Stacks 0814 で共通の基底中心上の étale 局所純変換から元の純変換へ戻す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- 各被覆項の二通りのテンソル基底変換のスカラー塔を照合する。
/--
概要：有限型アフィン始域を覆う有限平坦族の底変換で純変換が平坦なら、元の試験環上の純変換も平坦。
方針：被覆をテンソル積で底変換し、純変換と始域変更を交換して平坦性を降下する。
規約：試験環は Noether 環で、元の加群は有限型代数上有限。
使われ方：共通中心の標準チャートの平坦性を証明する。
-/
theorem modulePureTransform_flat_of_tensorSourceCover
    {R A B M ι : Type u} [CommRing R] [CommRing A] [CommRing B] [Finite ι]
    [Algebra R A] [Algebra R B] [IsNoetherianRing A] [Algebra.FiniteType R B]
    [AddCommGroup M] [Module B M] [Module.Finite B M]
    (D : ι → Type u) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)]
    [∀ i, Algebra B (D i)] [∀ i, IsScalarTower R B (D i)] [∀ i, Module.Flat B (D i)]
    (hcover : ∀ q : PrimeSpectrum B, ∃ (i : ι) (t : PrimeSpectrum (D i)),
      t.comap (algebraMap B (D i)) = q) (a : A)
    (hflat : ∀ i, let F := A ⊗[R] D i
      letI : Algebra (D i) F := Algebra.TensorProduct.rightAlgebra
      Module.Flat A (modulePureTransform (algebraMap A F a) (F ⊗[D i] (D i ⊗[B] M)))) :
    let E := A ⊗[R] B
    letI : Algebra B E := Algebra.TensorProduct.rightAlgebra
    Module.Flat A (modulePureTransform (algebraMap A E a) (E ⊗[B] M)) := by
  let E := A ⊗[R] B
  let F (i : ι) := A ⊗[R] D i
  let : Algebra B E := Algebra.TensorProduct.rightAlgebra
  let : ∀ i, Algebra (D i) (F i) := fun _ => Algebra.TensorProduct.rightAlgebra
  let : ∀ i, Algebra E (F i) := fun i => tensorRightBaseChangeAlgebra R A B (D i)
  let : ∀ i, Algebra B (F i) := fun i => Algebra.compHom (F i) (algebraMap B (D i))
  let : ∀ i, IsScalarTower B (D i) (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, IsScalarTower B E (F i) := fun i =>
    tensorRightBaseChange_isScalarTower_right R A B (D i)
  let : ∀ i, IsScalarTower A E (F i) := fun i =>
    tensorRightBaseChange_isScalarTower_left R A B (D i)
  let : ∀ i, Algebra.IsPushout B E (D i) (F i) := fun i =>
    tensorRightBaseChange_isPushout R A B (D i)
  let : ∀ i, Module.Flat E (F i) := fun i =>
    Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv B E (D i) (F i)).toLinearEquiv.symm
  have hcover' (p : PrimeSpectrum E) : ∃ (i : ι) (t : PrimeSpectrum (F i)),
      t.comap (algebraMap E (F i)) = p := by
    obtain ⟨i, q, hq⟩ := hcover (p.comap (algebraMap B E))
    have hp := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout B E (D i) (F i))
    obtain ⟨t, ht, _⟩ := Scheme.exists_preimage_of_isPullback hp p q hq.symm
    exact ⟨i, t, ht⟩
  let P := E ⊗[B] M
  let b := algebraMap A E a
  let : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing A E
  obtain ⟨n, hn⟩ := exists_pow_annihilates_boundaryTorsion_of_noetherian b P
  apply modulePureTransform_flat_of_flat_affine_cover F hcover' b n hn
  intro i
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange B E (F i) (F i) M
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange B (D i) (F i) (F i) M
  rw [← IsScalarTower.algebraMap_apply A E (F i)]
  let : Module.Flat A (modulePureTransform (algebraMap A (F i) a) (F i ⊗[D i] (D i ⊗[B] M))) :=
    hflat i
  exact Module.Flat.of_linearEquiv
    ((modulePureTransformCongr (algebraMap A (F i) a) (e₁.trans e₂.symm)).restrictScalars A)

end SerrePositivity.AlgebraicGeometry
