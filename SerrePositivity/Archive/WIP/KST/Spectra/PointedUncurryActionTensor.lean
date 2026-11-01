module

public import SerrePositivity.KST.Spectra.PointedBasedPathUncurry
public import SerrePositivity.KST.Spectra.InternalHomTensor

/-!
概要：元の区間の uncurry 作用を、同じテンソル curry 同型の逆射へ厳密同定する。
方針：懸垂作用と評価の同じ curry 式を展開し、閉構造の内部 uncurry と比較する。
規約：全 Hom の射の等式。使われ方：元の単位構造の実正方形を uncurry 座標へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 元の区間と三角形に使う uncurryAction は、同じテンソル curry 同型の逆射。 -/
lemma uncurryAction_eq_tensor_inv (A V : PointedSimplicialSet.{u}) :
    uncurryAction A V = (InternalHomTensor.iso PointedSimplicialSet.circle.{u} A V).inv := by
  rw [InternalHomTensor.iso_eq_ihomCurryIso]
  change curry ((α_ PointedSimplicialSet.circle.{u} A
      ((ihom A).obj ((ihom PointedSimplicialSet.circle.{u}).obj V))).hom ≫
        PointedSimplicialSet.circle.{u} ◁ (ihom.ev A).app
          ((ihom PointedSimplicialSet.circle.{u}).obj V)) ≫
      (ihom (suspension A)).map ((ihom.ev PointedSimplicialSet.circle.{u}).app V) =
    ihomUncurry PointedSimplicialSet.circle.{u} A V
  rw [← curry_natural_right]
  rfl

/-- 同じ uncurry 作用は、標的への後合成と厳密に可換。 -/
lemma uncurryAction_post (A : PointedSimplicialSet.{u})
    {V W : PointedSimplicialSet.{u}} (b : V ⟶ W) :
    PointedObject.basedHomMap A (PointedObject.basedHomMap PointedSimplicialSet.circle.{u} b) ≫
        uncurryAction A W =
      uncurryAction A V ≫ PointedObject.basedHomMap (suspension A) b := by
  rw [uncurryAction_eq_tensor_inv, uncurryAction_eq_tensor_inv]
  change (ihom A).map ((ihom PointedSimplicialSet.circle.{u}).map b) ≫
      (InternalHomTensor.iso PointedSimplicialSet.circle.{u} A W).inv =
    (InternalHomTensor.iso PointedSimplicialSet.circle.{u} A V).inv ≫
      (ihom (PointedSimplicialSet.circle.{u} ⊗ A)).map b
  have h := InternalHomTensor.natural_post PointedSimplicialSet.circle.{u} A b
  apply (cancel_mono (InternalHomTensor.iso PointedSimplicialSet.circle.{u} A W).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.Spectra.PointedMapping
