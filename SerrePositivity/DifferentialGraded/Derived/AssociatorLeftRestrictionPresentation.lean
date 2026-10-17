module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionKFlat
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionComputation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionResolution

/-! # 全導来外側左比較の逆を指定K-flatモデルへ計算する

## 概要
全導来外側左比較の逆を指定K-flatモデルへ計算する。

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
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E)

local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "L" => derivedBimoduleRestriction A B D B E (DGFunctor.id B) F

private lemma invert_model_square {V : Type*} [Category* V]
    {a b c d : V} (f : a ≅ b) (s : a ⟶ c) (t : b ⟶ d) (β : d ≅ c)
    (h : f.hom ≫ t = s ≫ β.inv) : f.inv ≫ s = t ≫ β.hom := by
  apply (Iso.cancel_iso_hom_left f _ _).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h]
  simp only [Category.assoc, β.inv_hom_id, Category.comp_id]

/-- 実際の全導来左比較の逆も、同じ指定モデルのsquareで計算される。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_inv_model_square :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
      (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q =
    (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q ≫
      (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom := by
  exact invert_model_square
    ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).app
      ((bimoduleToDerived A C E).obj Q.obj)) _ _
    (derivedComposeWithLeftRestrictionIso A B C E D F Q)
    (derivedBimoduleComposeLeftRestrictionIso_model_square A B C E D F hE hD Q)

/-- source表示は、固定K-flat合成の表示を出力の左制限へ送ったもの。 -/
lemma leftRestrictionDerivedComposeSourceBaseIso_hom_app :
    (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q =
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom L := by
  simp only [leftRestrictionDerivedComposeSourceBaseIso, Functor.isoWhiskerRight_hom,
    whiskerRight_app, rightKFlatComposePresentationIso_hom_app]
  rfl

/-- target表示は、後因子の制限表示の逆と、制限後K-flat因子の合成表示の合成。 -/
lemma leftRestrictionDerivedComposeTargetBaseIso_hom_app :
    (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q =
      (derivedBimoduleComposeFunctor A B C D hD).map
          ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) ≫
        (derivedBimoduleComposeKFlatIso A B C D hD LQ).hom := by
  simp only [leftRestrictionDerivedComposeTargetBaseIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, whiskerRight_app,
    whiskerLeft_app, Iso.symm_hom, rightKFlatComposePresentationIso_hom_app]
  rfl

/-- 全導来左比較の逆を、任意の導来前因子に自然な固定K-flat比較で計算する。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_inv_model_calculation :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom L =
    (derivedBimoduleComposeFunctor A B C D hD).map
        ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) ≫
      (derivedBimoduleComposeKFlatIso A B C D hD LQ).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom := by
  have h := derivedBimoduleComposeLeftRestrictionIso_inv_model_square A B C E D F hE hD Q
  rw [leftRestrictionDerivedComposeSourceBaseIso_hom_app,
    leftRestrictionDerivedComposeTargetBaseIso_hom_app] at h
  simpa only [Category.assoc] using h

/-- 全導来左比較の逆を、前因子は任意のまま通常比較と既存表示で計算する。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_inv_base_calculation
    (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
      (L).map (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    ((derivedBimoduleComposeFunctor A B C D hD).map
        ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj)).app
          ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C D hD LQ P).hom ≫
      (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫
      (middleLeftRestrictionDerivedIso A B E D F).hom.app
        ((composeWith A B C E Q.obj).obj P) := by
  have h := derivedBimoduleComposeLeftRestrictionIso_inv_model_square A B C E D F hE hD Q
  rw [leftRestrictionDerivedComposeSourceBaseIso_hom_app,
    leftRestrictionDerivedComposeTargetBaseIso_hom_app] at h
  have hc := NatTrans.congr_app h ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, whiskerRight_app,
    derivedComposeWithLeftRestrictionIso_base_app] at hc
  simpa only [derivedBimoduleComposeKFlatValueIso, Iso.app_hom, Category.assoc] using hc

end SerrePositivity.DifferentialGraded.BimoduleTensor
