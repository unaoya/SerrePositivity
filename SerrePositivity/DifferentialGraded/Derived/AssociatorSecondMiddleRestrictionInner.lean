module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionFactors
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionKFlat
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorComparison

/-! # 第二中間制限の内側全導来比較と指定K-flatモデルの表示

## 概要
第二中間制限の内側全導来比較と指定K-flatモデルの表示。

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
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hT : localHomKFlat A T) (Q : RightKFlatBimoduleCategory A C E)
  (R : RightKFlatBimoduleCategory A E T) (S : RightKFlatBimoduleCategory A D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)
  (hq : BimoduleCategory.quasiIso A D T q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "HD" => derivedBimoduleComposeFunctor A C D T hT
local notation "RRD" => Functor.obj
  (derivedBimoduleRestriction A D T E T F (DGFunctor.id T)) RT
local notation "LQD" => Functor.obj
  (derivedBimoduleRestriction A C D C E (DGFunctor.id C) F) QT
local notation "eS" => middleRestrictionKFlatFactorIso A E D T F R S q hq
local notation "KS" => rightKFlatDerivedCompose A C D T S
local notation "g" => middleRestrictionResolvedMap A C E D T F Q.obj R.obj S.obj q

/-- source表示を制限後Qの表示へ進めると、同じ二因子モデルの前半になる。 -/
lemma derivedSecondMiddleRestriction_inner_prefix_square :
    (middleRestrictionKFlatSourceIso A C E D T F hT R S q hq).hom.app QT ≫
      (KS).map ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) =
    ((HD).obj RRD).map ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) ≫
      ((HD).map (eS).hom).app ((bimoduleToDerived A C D).obj (LQ).obj) ≫
      (derivedBimoduleComposeKFlatIso A C D T hT S).hom.app
        ((bimoduleToDerived A C D).obj (LQ).obj) := by
  have h := ((HD).map (eS).hom ≫
    (derivedBimoduleComposeKFlatIso A C D T hT S).hom).naturality
      ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj)
  simp only [NatTrans.comp_app, Category.assoc] at h
  rw [middleRestrictionKFlatSourceIso_hom]
  simp only [whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  convert h.symm using 1 <;> rfl

/-- 内側の実際の全導来中間比較は、指定モデルで既存の通常解像度比較射へ計算される。 -/
lemma derivedSecondMiddleRestriction_inner_model_square :
    ((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT ≫
      (derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposeInnerComparisonIso A C D T hT LQ S
        ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm eS).hom ≫
      (bimoduleToDerived A C T).map g := by
  have hm := NatTrans.congr_app
    (derivedMiddleRestrictionNatTrans_kFlat_model_calculation A C E D T F hT R S q hq) QT
  simp only [NatTrans.comp_app] at hm
  rw [rightKFlatMiddleComparison_base_app] at hm
  have hp := derivedSecondMiddleRestriction_inner_prefix_square A C D E T F hT Q R S q hq
  rw [← Category.assoc
    ((middleRestrictionKFlatSourceIso A C E D T F hT R S q hq).hom.app QT), hp] at hm
  simp only [Category.assoc] at hm
  convert hm using 1 <;>
    simp only [derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
