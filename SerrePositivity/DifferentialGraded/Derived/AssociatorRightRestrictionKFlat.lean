module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionBase

/-! # 外側右制限は固定右K-flat因子の導来結合子を保つ

## 概要
外側右制限は固定右K-flat因子の導来結合子を保つ。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "QR" => rightKFlatCompose A C E T Q R

/-- 任意の導来前因子に自然な、外側右制限と固定K-flat結合子の可換square。 -/
lemma rightKFlatDerivedAssociator_rightRestriction :
    whiskerLeft RI (rightKFlatDerivedAssociator A D C E T Q R).hom ≫
      (derivedComposeWithRightRestrictionIso A B D C T F QR).hom =
    whiskerRight (derivedComposeWithRightRestrictionIso A B D C E F Q).hom
        (rightKFlatDerivedCompose A D E T R) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithRightRestrictionIso A B D E T F R).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E T Q R).hom RO := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [derivedComposeWithRightRestrictionIso_base_app,
    derivedComposeWithRightRestrictionIso_base_app]
  let PQ := (composeWith A B C E Q.obj).obj P
  have hβ := derivedComposeWithRightRestrictionIso_base_app A B D E T F R PQ
  have hαB := rightKFlatDerivedAssociator_base_app A B C E T Q R P
  erw [hβ, hαB]
  have ha := (rightKFlatDerivedAssociator A D C E T Q R).hom.naturality
    ((middleRightRestrictionDerivedIso A B D F C).inv.app P)
  simp only [Functor.comp_map] at ha
  simp only [Category.assoc]
  have hαD := rightKFlatDerivedAssociator_base_app A D C E T Q R
    ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)
  rw [← reassoc_of% ha]
  erw [hαD]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hc := ((rightKFlatDerivedCompose A D E T R).mapIso
    ((middleRightRestrictionDerivedIso A B D F E).app PQ)).hom_inv_id
  simp only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv] at hc
  rw [reassoc_of% hc]
  have hmap := rightKFlatDerivedCompose_map_base A D E T R
    (composeRightRestrictionIso A B D C E F P Q.obj).hom
  rw [hmap]
  have h := associatorRightRestriction_localized_square A B D C E F T P Q.obj R.obj
  have hh := congrArg (fun k =>
    (rightKFlatDerivedCompose A D E T R).map
      ((rightKFlatDerivedCompose A D C E Q).map
        ((middleRightRestrictionDerivedIso A B D F C).inv.app P)) ≫ k) h
  convert hh using 1
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
