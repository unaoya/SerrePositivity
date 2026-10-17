module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionNested

/-! # 外側左制限と全導来結合子の二段階合成側のモデルsquare

## 概要
外側左制限と全導来結合子の二段階合成側のモデルsquare。

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
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G

private lemma paste_pair {V W X : Type*} [Category* V] [Category* W] [Category* X]
    {U V' : V ⥤ W} (a : U ⟶ V') {S T K K' T' : W ⥤ X}
    (b : S ⟶ T) (out : T ⟶ T') (u : S ⟶ K) (v : K ⟶ K') (w : K' ⟶ T')
    (hm : b ≫ out = u ≫ v ≫ w) :
    whiskerLeft U b ≫ whiskerRight a T ≫ whiskerLeft V' out =
      whiskerLeft U u ≫ whiskerRight a K ≫ whiskerLeft V' v ≫ whiskerLeft V' w := by
  apply NatTrans.ext
  funext Y
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  have h := NatTrans.congr_app hm (V'.obj Y)
  simp only [NatTrans.comp_app] at h
  calc
    _ = S.map (a.app Y) ≫ b.app (V'.obj Y) ≫ out.app (V'.obj Y) := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ out.app (V'.obj Y)) (b.naturality (a.app Y)).symm
    _ = S.map (a.app Y) ≫ u.app (V'.obj Y) ≫ v.app (V'.obj Y) ≫ w.app (V'.obj Y) := by
      rw [h]
    _ = _ := by
      rw [← Category.assoc (S.map (a.app Y)) (u.app (V'.obj Y)), u.naturality,
        Category.assoc]

/-- 実際の全導来左比較は、二段階合成の表示を通すと固定モデルの比較に戻る。 -/
lemma derivedLeftRestriction_pair_model_square :
    whiskerLeft
        ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
        ((derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv.app
          ((bimoduleToDerived A E T).obj R.obj)) ≫
      whiskerRight (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom L =
    (derivedBimoduleComposePairComparisonIso A B C E D hE hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithLeftRestrictionIso A B E T D G R).hom := by
  have hm := derivedBimoduleComposeLeftRestrictionIso_inv_model_calculation
    A B E T D G hT hD R
  have h := paste_pair (derivedBimoduleComposeKFlatIso A B C E hE Q).hom
    _ _ _ _ _ hm
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Iso.symm_hom, Iso.app_inv,
      CategoryTheory.Functor.map_id, whiskerLeft_id', whiskerRight_id', whiskerRight_comp,
      Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
