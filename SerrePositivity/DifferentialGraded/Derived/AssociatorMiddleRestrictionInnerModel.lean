module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionFactors
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionInner

/-! # 第一中間制限の全導来内側比較と指定二因子モデルの表示

## 概要
第一中間制限の全導来内側比較と指定二因子モデルの表示。

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
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hT : localHomKFlat A T) (Q : RightKFlatBimoduleCategory A C E)
  (S : RightKFlatBimoduleCategory A D E) (R : RightKFlatBimoduleCategory A E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "RI" => derivedBimoduleRestriction A D T C T F (DGFunctor.id T)
local notation "HR" => Functor.obj (derivedBimoduleComposeFunctor A D E T hT) RT
local notation "eS" => middleRestrictionKFlatFactorIso A C D E F Q S q hq
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "qR" => middleRestrictionComposeAugmentation A C D E T F Q.obj S.obj R.obj q

/-- 内側の全導来右比較は、指定二因子の表示を通すと合成増大の局所化になる。 -/
lemma derivedMiddleRestriction_inner_model_square :
    ((derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom.app RT).app QT ≫
      (RI).map (derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposeInnerComparisonIso A D E T hT S R eS (Iso.refl _)).hom ≫
      (bimoduleToDerived A D T).map qR ≫
      (middleRightRestrictionDerivedIso A C D F T).hom.app (QR).obj := by
  have hs := middleRestrictionInnerAugmentation_model_square A C D E T F hT Q.obj S.obj R q
  rw [← middleRestrictionKFlatFactorIso_inv A C D E F Q S q hq] at hs
  have hc := congrArg (fun k => (HR).map k) (eS).hom_inv_id
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  have h := congrArg (fun k => (HR).map (eS).hom ≫ k) hs
  rw [reassoc_of% hc] at h
  convert h using 1 <;>
    simp only [derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom,
    Iso.app_hom, CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
