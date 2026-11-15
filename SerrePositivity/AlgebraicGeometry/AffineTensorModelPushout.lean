module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：実際の tensor 模型を、同じ構造射の環の pushout 正方形へ移す。
方針：Mathlib の tensor の普遍性を、指定された代数同型で移送する。
規約：R-代数構造と右挿入との合成を保持する。
使われ方：B03・B04 の filtered pushout の頂点を実際の模型に保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 実際の tensor 模型による、同じ環の構造射の pushout 正方形。 -/
theorem isPushout_affineTensorModel
    {A R S C : Type u} [CommRing A] [CommRing R] [CommRing S] [CommRing C]
    [Algebra A R] [Algebra A S] [Algebra R C] (e : R ⊗[A] S ≃ₐ[R] C) :
    IsPushout (CommRingCat.ofHom (algebraMap A R))
      (CommRingCat.ofHom (algebraMap A S))
      (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S).toRingHom)) := by
  have H := IsPushout.of_isColimit (CommRingCat.pushoutCoconeIsColimit A R S)
  apply H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    e.toRingEquiv.toCommRingCatIso
  · rfl
  · rfl
  · ext r
    exact e.commutes r
  · rfl

end SerrePositivity.AlgebraicGeometry
