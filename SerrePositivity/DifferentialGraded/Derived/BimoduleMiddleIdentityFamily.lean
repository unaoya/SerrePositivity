module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCanonicalComposition

/-! # 恒等中間比較の解像度を含まないsource同型を関手族へ束ねる

## 概要
恒等中間比較の解像度を含まないsource同型を関手族へ束ねる。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

/-- 左右の恒等制限の自然同型だけから構成する、閉零両因子上のsource正規化同型。 -/
def middleClosedIdentityIso :
    middleClosedSourceFunctor A B D D L (DGFunctor.id D) hL ≅
      bimoduleToDerived A D L ⋙ derivedBimoduleComposeFunctor A B D L hL ⋙
        (whiskeringLeft _ _ _).obj (bimoduleToDerived A B D) :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (BimoduleCategory.middleRightRestrictionIdIso A D L)
        (bimoduleToDerived A D L) ≪≫ Functor.leftUnitor _)
      (derivedBimoduleComposeFunctor A B D L hL ⋙
        (whiskeringLeft _ _ _).obj
          (BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D) ⋙
            bimoduleToDerived A B D)) ≪≫
    Functor.isoWhiskerLeft (bimoduleToDerived A D L ⋙ derivedBimoduleComposeFunctor A B D L hL)
      ((whiskeringLeft _ _ _).mapIso
        (Functor.isoWhiskerRight (BimoduleCategory.middleLeftRestrictionIdIso A B D)
          (bimoduleToDerived A B D) ≪≫ Functor.leftUnitor _))

lemma middleClosedIdentityIso_hom_app (Q : BimoduleCategory A D L)
    (P : BimoduleCategory A B D) :
    ((middleClosedIdentityIso A B D L hL).hom.app Q).app P =
      (derivedMiddleIdentitySourceIso A B D L hL P Q).hom := by
  change (((derivedBimoduleComposeFunctor A B D L hL).map
    ((bimoduleToDerived A D L).map
      (BimoduleCategory.middleRightRestrictionIdObjIso A D L Q).hom ≫ 𝟙 _)).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B D D (DGFunctor.id D)).obj P)) ≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q)).map
      ((bimoduleToDerived A B D).map
        (BimoduleCategory.middleLeftRestrictionIdObjIso A B D P).hom ≫ 𝟙 _)) = _
  rw [Category.comp_id, Category.comp_id]
  rfl

/-- 指定右K-flat後因子について、恒等比較のsourceを閉零前因子の関手上で正規化する。 -/
def middleIdentitySourceFamilyIso (Q : RightKFlatBimoduleCategory A D L) :
    middleDerivedSourceFamily A B D D L (DGFunctor.id D) hL Q ≅
      middleDerivedTargetFamily A B D L hL Q :=
  (middleClosedIdentityIso A B D L hL).app Q.obj

lemma derivedMiddleRestrictionCanonicalFamily_functor_id (Q : RightKFlatBimoduleCategory A D L) :
    derivedMiddleRestrictionCanonicalFamily A B D D L (DGFunctor.id D) hL Q =
      (middleIdentitySourceFamilyIso A B D L hL Q).hom := by
  apply NatTrans.ext
  funext P
  rw [derivedMiddleRestrictionCanonicalFamily_app,
    derivedMiddleRestrictionCanonicalComparison_functor_id]
  exact (middleClosedIdentityIso_hom_app A B D L hL Q.obj P).symm

/-- 前因子の全導来圏へ、左右の恒等制限のsource正規化同型を降ろす。 -/
def middleIdentitySourceLiftIso (Q : RightKFlatBimoduleCategory A D L) :
    middleDerivedSourceLift A B D D L (DGFunctor.id D) hL Q ≅
      (derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q.obj) :=
  Localization.liftNatIso (bimoduleToDerived A B D) (BimoduleCategory.quasiIso A B D)
    (middleDerivedSourceFamily A B D D L (DGFunctor.id D) hL Q)
    (middleDerivedTargetFamily A B D L hL Q)
    (middleDerivedSourceLift A B D D L (DGFunctor.id D) hL Q)
    ((derivedBimoduleComposeFunctor A B D L hL).obj ((bimoduleToDerived A D L).obj Q.obj))
    (middleIdentitySourceFamilyIso A B D L hL Q)

lemma derivedMiddleRestrictionCanonicalLocalized_functor_id
    (Q : RightKFlatBimoduleCategory A D L) :
    derivedMiddleRestrictionCanonicalLocalized A B D D L (DGFunctor.id D) hL Q =
      (middleIdentitySourceLiftIso A B D L hL Q).hom := by
  rw [← derivedMiddleRestrictionCanonicalFamily_lift,
    derivedMiddleRestrictionCanonicalFamily_functor_id]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
