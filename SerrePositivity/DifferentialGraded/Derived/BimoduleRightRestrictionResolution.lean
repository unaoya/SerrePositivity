module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolution

/-! # 外側右制限の全導来比較を任意の指定K-flat解像度で計算する

## 概要
外側右制限の全導来比較を任意の指定K-flat解像度で計算する。

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
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (Q : BimoduleCategory A C E)
  (R : RightKFlatBimoduleCategory A C E) (q : R.obj ⟶ Q)
  (hq : BimoduleCategory.quasiIso A C E q)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D E B E F (DGFunctor.id E)

/-- 右K-flatモデルでの前合成表示は、既存の固定因子計算同型そのもの。 -/
lemma rightKFlatComposePresentationIso_hom_app :
    (rightKFlatComposePresentationIso A C E hE B).hom.app R =
      (derivedBimoduleComposeKFlatIso A B C E hE R).hom := by
  simp only [rightKFlatComposePresentationIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    eqToHom_app]
  change (derivedBimoduleComposeFunctor A B C E hE).map (𝟙 _) ≫
    (derivedBimoduleComposeKFlatIso A B C E hE R).hom ≫ 𝟙 _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- 全導来外側右制限比較と、任意の指定右K-flat解像度の計算同型とのsquare。 -/
lemma derivedBimoduleComposeRightRestrictionIso_resolution_square :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q) ≫
      whiskerRight (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom RO =
    whiskerLeft RI (derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq).hom ≫
      (derivedComposeWithRightRestrictionIso A B D C E F R).hom := by
  let S := rightRestrictionDerivedComposeSource A B D C E F hE
  let T := rightRestrictionDerivedComposeTarget A B D C E F hE
  let u := (bimoduleToDerived A C E).map q
  have hn := (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.naturality u
  have hs := congrArg (fun k => whiskerLeft RI k)
    (derivedBimoduleComposeResolutionComputation_fac A D C E hE Q R q hq)
  have ht := congrArg (fun k => whiskerRight k RO)
    (derivedBimoduleComposeResolutionComputation_fac A B C E hE Q R q hq)
  apply (Iso.cancel_iso_hom_left (S.mapIso (bimoduleDerivedIso A C E q hq)) _ _).1
  change S.map u ≫ (_ ≫ _) = S.map u ≫ (_ ≫ _)
  rw [← Category.assoc, hn, Category.assoc]
  have ht' : T.map u ≫
      whiskerRight (derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom RO =
    (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app R := by
    simpa only [S, T, u, whiskeringRight_obj_map, rightRestrictionDerivedComposeTarget,
      rightRestrictionDerivedComposeTargetBaseIso,
      Functor.comp_map, Functor.isoWhiskerRight_hom, whiskerRight_app,
      rightKFlatComposePresentationIso_hom_app, whiskerRight_comp] using ht
  rw [ht', ← Category.assoc]
  have hs' : S.map u ≫
      whiskerLeft RI (derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq).hom =
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app R := by
    simpa only [S, T, u, whiskeringLeft_obj_map, rightRestrictionDerivedComposeSource,
      rightRestrictionDerivedComposeSourceBaseIso,
      Functor.comp_map, Functor.isoWhiskerRight_hom, whiskerRight_app,
      rightKFlatComposePresentationIso_hom_app, whiskerLeft_comp] using hs
  rw [hs']
  exact derivedBimoduleComposeRightRestrictionIso_model_square A B D C E F hE R

/-- 元の前因子上では、任意解像度による全導来外側比較は通常の比較射に計算できる。 -/
lemma derivedBimoduleComposeRightRestrictionIso_resolution_app_calc
    (P : BimoduleCategory A B C) :
    (derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq).inv.app
        ((bimoduleToDerived A D C).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)) ≫
      ((derivedBimoduleComposeFunctor A D C E hE).obj ((bimoduleToDerived A C E).obj Q)).map
        ((middleRightRestrictionDerivedIso A B D F C).hom.app P) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q)).app ((bimoduleToDerived A B C).obj P) ≫
      (RO).map ((derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq).hom.app
        ((bimoduleToDerived A B C).obj P)) =
    (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P R.obj).hom ≫
      (middleRightRestrictionDerivedIso A B D F E).hom.app
        ((composeWith A B C E R.obj).obj P) := by
  let cD := derivedBimoduleComposeResolutionComputation A D C E hE Q R q hq
  let cB := derivedBimoduleComposeResolutionComputation A B C E hE Q R q hq
  let e := (middleRightRestrictionDerivedIso A B D F C).app P
  let V := derivedComposeWith A D C E R.obj R.property
  have hn := cD.inv.naturality e.hom
  have hc := NatTrans.congr_app
    (derivedBimoduleComposeRightRestrictionIso_resolution_square A B D C E F hE Q R q hq)
    ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hc
  have h : cD.inv.app ((RI).obj ((bimoduleToDerived A B C).obj P)) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q)).app ((bimoduleToDerived A B C).obj P) ≫
      (RO).map (cB.hom.app ((bimoduleToDerived A B C).obj P)) =
    (derivedComposeWithRightRestrictionIso A B D C E F R).hom.app
      ((bimoduleToDerived A B C).obj P) := by
    rw [hc]
    exact (cD.app ((RI).obj ((bimoduleToDerived A B C).obj P))).inv_hom_id_assoc _
  change cD.inv.app ((BimoduleCategory.middleRightRestrictionFunctor A B D C F ⋙
    bimoduleToDerived A D C).obj P) ≫
    ((derivedBimoduleComposeFunctor A D C E hE).obj
      ((bimoduleToDerived A C E).obj Q)).map e.hom ≫ _ ≫ _ = _
  erw [← Category.assoc (cD.inv.app _), ← hn, Category.assoc, h]
  rw [derivedComposeWithRightRestrictionIso_hom_app_calc]
  change V.map e.hom ≫ (V.map e.inv ≫ 𝟙 _ ≫ _ ≫ _ ≫ (RO).map (𝟙 _)) = _
  rw [← Category.assoc, ← V.map_comp, e.hom_inv_id, V.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
