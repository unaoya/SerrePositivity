module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionNested

/-! # 第一中間制限と全導来結合子の二段階合成側のモデルsquare

## 概要
第一中間制限と全導来結合子の二段階合成側のモデルsquare。

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
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (S : RightKFlatBimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "eS" => middleRestrictionKFlatFactorIso A C D E F Q S q hq

private lemma paste_pair {V W X : Type*} [Category* V] [Category* W] [Category* X]
    {F G J K : V ⥤ W} (a : F ⟶ G) (b : G ⟶ K) (c : F ⟶ J) (d : J ⟶ K)
    (H H' : W ⥤ X) (r : H ⟶ H') (hm : a ≫ b = c ≫ d) :
    whiskerRight a H ≫ whiskerRight b H ≫ whiskerLeft K r =
      whiskerRight c H ≫ whiskerLeft J r ≫ whiskerRight d H' := by
  apply NatTrans.ext
  funext P
  have h := congrArg (fun k => H.map k ≫ r.app (K.obj P)) (NatTrans.congr_app hm P)
  simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp] at h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  calc
    _ = H.map (c.app P) ≫ H.map (d.app P) ≫ r.app (K.obj P) := by
      simpa only [Category.assoc] using h
    _ = _ := by rw [r.naturality]

/-- 二段階合成の既存表示を通すと、実際の中間比較が指定K-flatモデルの比較に戻る。 -/
lemma derivedMiddleRestriction_pair_model_square :
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app QT)
        ((derivedBimoduleComposeFunctor A B E T hT).obj RT) ≫
      (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    whiskerLeft L (derivedBimoduleComposePairComparisonIso A B D E T hE hT S R
        eS (Iso.refl _)).hom ≫
      whiskerRight (rightKFlatMiddleComparison A B C D E F Q S q)
        (rightKFlatDerivedCompose A B E T R) := by
  have hm := derivedMiddleRestrictionNatTrans_kFlat_model_calculation A B C D E F hE Q S q hq
  rw [middleRestrictionKFlatSourceIso_hom] at hm
  have h := paste_pair _ _ _ _ _ _ (derivedBimoduleComposeKFlatIso A B E T hT R).hom hm
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
      whiskerLeft_id', whiskerRight_id', whiskerLeft_comp, whiskerRight_comp,
      Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
