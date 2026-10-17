module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionBase

/-! # 外側右制限の固定K-flat合成比較の後因子自然性

## 概要
外側右制限の固定K-flat合成比較の後因子自然性。

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

lemma derivedComposeWithRightRestrictionIso_hom_app_calc
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWith A D C E Q.obj Q.property).map
          ((middleRightRestrictionDerivedIso A B D F C).inv.app P) ≫
        (derivedComposeWithComputation A D C E Q.obj Q.property
          ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)).hom ≫
        (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P Q.obj).hom ≫
        (middleRightRestrictionDerivedIso A B D F E).hom.app
          ((composeWith A B C E Q.obj).obj P) ≫
        (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map
          (derivedComposeWithComputation A B C E Q.obj Q.property P).inv := by
  rw [derivedComposeWithRightRestrictionIso_hom_app]
  simp only [derivedComposeWithRightRestrictionPreIso, composeWithRightRestrictionLocalizedIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
  rfl

/-- 前因子を既存の導来制限で送ってから合成する固定後因子関手族。 -/
def rightRestrictionKFlatComposeSource : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedComposeWithFunctor A D C E ⋙
    (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 合成の出力を既存の導来制限で送る固定後因子関手族。 -/
def rightRestrictionKFlatComposeTarget : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D E) :=
  derivedComposeWithFunctor A B C E ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D E B E F (DGFunctor.id E))

lemma derivedComposeWithRightRestrictionIso_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    (rightRestrictionKFlatComposeSource A B D C E F).map g ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q').hom =
      (derivedComposeWithRightRestrictionIso A B D C E F Q).hom ≫
        (rightRestrictionKFlatComposeTarget A B D C E F).map g := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  change (derivedComposeWithMap A D C E Q.property Q'.property g.hom).app
        ((derivedBimoduleRestriction A D C B C F (DGFunctor.id C)).obj
          ((bimoduleToDerived A B C).obj P)) ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q').hom.app
          ((bimoduleToDerived A B C).obj P) =
    (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map
        ((derivedComposeWithMap A B C E Q.property Q'.property g.hom).app
          ((bimoduleToDerived A B C).obj P))
  rw [derivedComposeWithRightRestrictionIso_hom_app_calc,
    derivedComposeWithRightRestrictionIso_hom_app_calc]
  have hn := (derivedComposeWithMap A D C E Q.property Q'.property g.hom).naturality
    ((middleRightRestrictionDerivedIso A B D F C).inv.app P)
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  simp only [derivedComposeWithMap_app, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have h₀ := congrArg ((bimoduleToDerived A D E).map)
    (composeRightRestrictionIso_naturality A B D C E F (𝟙 P) g.hom)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at h₀
  have h₁ := (middleRightRestrictionDerivedIso A B D F E).hom.naturality
    (composeMap A B C E (𝟙 P) g.hom)
  simp only [Functor.comp_map] at h₁
  have hh := (congrArg (fun k => k ≫
      (middleRightRestrictionDerivedIso A B D F E).hom.app
        ((composeWith A B C E Q'.obj).obj P)) h₀).trans (by
    simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
      Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
      (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P Q.obj).hom ≫ k) h₁)
  simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
    Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
    (derivedComposeWith A D C E Q.obj Q.property).map
        ((middleRightRestrictionDerivedIso A B D F C).inv.app P) ≫
      (derivedComposeWithComputation A D C E Q.obj Q.property
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)).hom ≫ k ≫
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map
        (derivedComposeWithComputation A B C E Q'.obj Q'.property P).inv) hh

/-- 外側右制限の比較を、右K-flat後因子にも自然な自然同型へ束ねる。 -/
def rightRestrictionKFlatComposeIso :
    rightRestrictionKFlatComposeSource A B D C E F ≅
      rightRestrictionKFlatComposeTarget A B D C E F :=
  NatIso.ofComponents (derivedComposeWithRightRestrictionIso A B D C E F) (by
    intro Q Q' g
    exact derivedComposeWithRightRestrictionIso_naturality A B D C E F g)

end SerrePositivity.DifferentialGraded.BimoduleTensor
