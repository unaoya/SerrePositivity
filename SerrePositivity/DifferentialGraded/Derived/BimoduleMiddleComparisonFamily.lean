module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleNaturality

/-! # 指定解像度による導来中間圏比較の前因子に関する自然変換

## 概要
指定解像度による導来中間圏比較の前因子に関する自然変換。

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
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)

def middleDerivedSourceFamily : BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ bimoduleToDerived A B D ⋙
    (derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))

def middleDerivedTargetFamily : BimoduleCategory A B C ⥤ DerivedBimoduleCategory A B E :=
  bimoduleToDerived A B C ⋙
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj)

variable (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

/-- sourceの計算同型を、既存の導来合成計算の自然同型から構成する。 -/
def middleDerivedSourceFamilyIso :
    middleDerivedSourceFamily A B C D E F hE Q ≅
      (BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙ composeWith A B D E R.obj) ⋙
        bimoduleToDerived A B E :=
  Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
    (Functor.isoWhiskerLeft (bimoduleToDerived A B D)
      (derivedBimoduleComposeResolutionComputation A B D E hE _ R q hq) ≪≫
        eqToIso (derivedComposeWith_fac A B D E R.obj R.property)) ≪≫
    (Functor.associator _ _ _).symm

/-- targetの計算同型も既存のK-flat因子での計算を使う。 -/
def middleDerivedTargetFamilyIso :
    middleDerivedTargetFamily A B C E hE Q ≅ composeWith A B C E Q.obj ⋙ bimoduleToDerived A B E :=
  Functor.isoWhiskerLeft (bimoduleToDerived A B C)
    (derivedBimoduleComposeKFlatIso A B C E hE Q) ≪≫
      eqToIso (derivedComposeWith_fac A B C E Q.obj Q.property)

/-- 既存の実際の導来合成間の比較は、前因子の閉零圏上で自然。 -/
def derivedMiddleRestrictionComparisonFamily :
    middleDerivedSourceFamily A B C D E F hE Q ⟶ middleDerivedTargetFamily A B C E hE Q :=
  (middleDerivedSourceFamilyIso A B C D E F hE Q R q hq).hom ≫
    whiskerRight (middleRestrictionResolvedNatTrans A B C D E F Q.obj R.obj q)
      (bimoduleToDerived A B E) ≫
        (middleDerivedTargetFamilyIso A B C E hE Q).inv

lemma derivedMiddleRestrictionComparisonFamily_app (P : BimoduleCategory A B C) :
    (derivedMiddleRestrictionComparisonFamily A B C D E F hE Q R q hq).app P =
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq := by
  simp only [derivedMiddleRestrictionComparisonFamily, middleDerivedSourceFamilyIso,
    middleDerivedTargetFamilyIso, derivedMiddleRestrictionComparison,
    middleRestrictionSourceComputation, derivedBimoduleComposeKFlatValueIso,
    derivedComposeWithComputation, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app, Iso.app_hom, Iso.app_inv,
    eqToIso.hom, eqToIso.inv, eqToHom_refl, NatTrans.id_app, Category.comp_id, Category.id_comp,
    middleRestrictionResolvedNatTrans, Category.assoc]
  exact congrArg (fun k =>
    (derivedBimoduleComposeResolutionComputation A B D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj) R q hq).hom.app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫ k)
    (Category.id_comp ((bimoduleToDerived A B E).map
      (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) ≫
        (derivedBimoduleComposeKFlatIso A B C E hE Q).inv.app
          ((bimoduleToDerived A B C).obj P))).symm

end SerrePositivity.DifferentialGraded.BimoduleTensor
