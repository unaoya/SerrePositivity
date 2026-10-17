module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionNested

/-! # 外側右制限と二段階全導来合成の表示

## 概要
外側右制限と二段階全導来合成の表示。

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
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj

private lemma paste_horizontal {V W X : Type*} [Category* V] [Category* W] [Category* X]
    (U : W ⥤ V) (H K : V ⥤ X) (J L : W ⥤ X)
    (b : U ⋙ H ⟶ J) (b' : U ⋙ K ⟶ L) (k : H ⟶ K) (l : J ⟶ L)
    (hb : b ≫ l = whiskerLeft U k ≫ b')
    {x x' : V} {y y' : W} (a : x ⟶ U.obj y) (v : y ⟶ y')
    (w : x ⟶ x') (a' : x' ⟶ U.obj y') (ha : a ≫ U.map v = w ≫ a') :
    H.map a ≫ b.app y ≫ J.map v ≫ l.app y' =
      H.map w ≫ k.app x' ≫ K.map a' ≫ b'.app y' := by
  have hn := b.naturality v
  have hm := congrArg H.map ha
  have hc := NatTrans.congr_app hb y'
  simp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp] at hm
  simp only [NatTrans.comp_app, whiskerLeft_app] at hc
  calc
    _ = H.map a ≫ H.map (U.map v) ≫ b.app y' ≫ l.app y' := by
      rw [← reassoc_of% hn]
    _ = H.map w ≫ H.map a' ≫ b.app y' ≫ l.app y' := by
      rw [← Category.assoc (H.map a), hm, Category.assoc]
    _ = H.map w ≫ H.map a' ≫ k.app (U.obj y') ≫ b'.app y' := by rw [hc]
    _ = _ := by rw [← reassoc_of% (k.naturality a')]

/-- 二段階の全導来右比較は、両側の合成表示を通すと固定K-flat比較に戻る。 -/
lemma derivedRightRestriction_pair_model_square :
    whiskerRight
        ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app QT)
        ((derivedBimoduleComposeFunctor A D E T hT).obj RT) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app RT) ≫
      whiskerRight (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom RO =
    whiskerLeft RI (derivedBimoduleComposePairComparisonIso A D C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom ≫
      whiskerRight (derivedComposeWithRightRestrictionIso A B D C E F Q).hom
        (rightKFlatDerivedCompose A D E T R) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithRightRestrictionIso A B D E T F R).hom := by
  apply NatTrans.ext
  funext P
  have hq := NatTrans.congr_app
    (derivedBimoduleComposeRightRestrictionIso_model_calculation A B D C E F hE Q) P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hq
  have hr := derivedBimoduleComposeRightRestrictionIso_model_calculation A B D E T F hT R
  have h := paste_horizontal _ _ _ _ _ _ _ _ _ hr _ _ _ _ hq
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, whiskerLeft_id', whiskerRight_id',
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.id_comp,
      CategoryTheory.Functor.map_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
