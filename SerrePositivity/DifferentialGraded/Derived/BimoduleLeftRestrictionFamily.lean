module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionBase

/-! # 外側左制限の導来合成比較を右K-flat後因子の関手族へ束ねる

## 概要
外側左制限の導来合成比較を右K-flat後因子の関手族へ束ねる。

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

/-- 元の前因子上で、固定K-flat後因子の比較を既存の計算同型で表示する。 -/
lemma derivedComposeWithLeftRestrictionIso_hom_app_calc
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (derivedComposeWithComputation A B C D
          ((rightKFlatLeftRestriction A C E D F).obj Q).obj
          ((rightKFlatLeftRestriction A C E D F).obj Q).property P).hom ≫
        (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫
        (middleLeftRestrictionDerivedIso A B E D F).hom.app
          ((composeWith A B C E Q.obj).obj P) ≫
        (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
          (derivedComposeWithComputation A B C E Q.obj Q.property P).inv := by
  rw [derivedComposeWithLeftRestrictionIso_hom_app]
  simp only [derivedComposeWithLeftRestrictionPreIso, composeWithLeftRestrictionLocalizedIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Category.assoc]
  rfl

/-- 先に外側左制限してから固定因子の導来合成を行う関手族。 -/
def leftRestrictionKFlatComposeSource : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  rightKFlatLeftRestriction A C E D F ⋙ derivedComposeWithFunctor A B C D

/-- 固定因子の導来合成を行い、その出力の外側左作用を制限する関手族。 -/
def leftRestrictionKFlatComposeTarget : RightKFlatBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A B D) :=
  derivedComposeWithFunctor A B C E ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F)

/-- 右K-flat後因子の任意の射に関する、実際の導来合成比較の自然性。 -/
lemma derivedComposeWithLeftRestrictionIso_naturality
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    (leftRestrictionKFlatComposeSource A B C E D F).map g ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q').hom =
      (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom ≫
        (leftRestrictionKFlatComposeTarget A B C E D F).map g := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  change (derivedComposeWithMap A B C D
      ((rightKFlatLeftRestriction A C E D F).obj Q).property
      ((rightKFlatLeftRestriction A C E D F).obj Q').property
      ((BimoduleCategory.middleLeftRestrictionFunctor A C E D F).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q').hom.app
          ((bimoduleToDerived A B C).obj P) =
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
        ((derivedComposeWithMap A B C E Q.property Q'.property g.hom).app
          ((bimoduleToDerived A B C).obj P))
  simp only [derivedComposeWithMap_app, derivedComposeWithLeftRestrictionIso_hom_app_calc,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map_comp_assoc,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have h₀ := congrArg ((bimoduleToDerived A B D).map)
    (composeLeftRestrictionIso_naturality A B C E D F (𝟙 P) g.hom)
  simp only [CategoryTheory.Functor.map_comp] at h₀
  have h₁ := (middleLeftRestrictionDerivedIso A B E D F).hom.naturality
    (composeMap A B C E (𝟙 P) g.hom)
  simp only [Functor.comp_map] at h₁
  have hn := (congrArg (fun k => k ≫
      (middleLeftRestrictionDerivedIso A B E D F).hom.app
        ((composeWith A B C E Q'.obj).obj P)) h₀).trans (by
    simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
      Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
      (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫ k) h₁)
  simpa only [Category.assoc, composeWith, composeFunctor, Functor.comp_obj,
      Functor.prod', Functor.const, Functor.id_obj] using congrArg (fun k =>
    (derivedComposeWithComputation A B C D
        ((rightKFlatLeftRestriction A C E D F).obj Q).obj
        ((rightKFlatLeftRestriction A C E D F).obj Q).property P).hom ≫ k ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
        (derivedComposeWithComputation A B C E Q'.obj Q'.property P).inv) hn

/-- 外側左制限の比較を、右K-flat後因子にも自然な自然同型へ束ねる。 -/
def leftRestrictionKFlatComposeIso :
    leftRestrictionKFlatComposeSource A B C E D F ≅ leftRestrictionKFlatComposeTarget A B C E D F :=
  NatIso.ofComponents (derivedComposeWithLeftRestrictionIso A B C E D F) (by
    intro Q Q' g
    exact derivedComposeWithLeftRestrictionIso_naturality A B C E D F g)

end SerrePositivity.DifferentialGraded.BimoduleTensor
