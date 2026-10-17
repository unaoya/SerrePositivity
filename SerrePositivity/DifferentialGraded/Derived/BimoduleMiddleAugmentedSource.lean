module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCompositePresentation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCanonicalComposition

/-! # 制限後の指定モデルから二段階の全導来sourceへの増大

## 概要
制限後の指定モデルから二段階の全導来sourceへの増大。

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
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 増大をさらにFで制限し、閉零表示同型を通じて全導来sourceへ送る。 -/
def middleIteratedAugmentedSourceMap
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : BimoduleCategory A E L)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj R))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ⟶
    ((middleIteratedDerivedSource A B D E T L F G hL).obj
      ((bimoduleToDerived A T L).obj Q)).obj ((bimoduleToDerived A B T).obj P) :=
  ((derivedBimoduleComposeFunctor A B D L hL).map
      ((bimoduleToDerived A D L).map
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).map q))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≫
    (middleIteratedClosedSourceIso A B D E T L F G hL Q P).hom

/-- 全導来sourceの正規化は、指定モデルに対する既存の合成source同型と可換。 -/
lemma middleIteratedAugmentedSourceMap_normalize
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : BimoduleCategory A E L)
    (q : R ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)
    (hq : BimoduleCategory.quasiIso A E L q) :
    middleIteratedAugmentedSourceMap A B D E T L F G hL Q P R q ≫
        ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app
          ((bimoduleToDerived A T L).obj Q)).app ((bimoduleToDerived A B T).obj P) =
      (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q R q hq).hom ≫
        ((middleClosedSourceIdentification A B T D L (F.comp G) hL).hom.app Q).app P := by
  unfold middleIteratedAugmentedSourceMap
  rw [Category.assoc, middleIteratedClosedSourceIso_normalize]
  simp only [derivedMiddleCompositeSourceIso, middleIteratedClosedNormalizationIso,
    BimoduleCategory.middleRightRestrictionCompositeMap, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, bimoduleDerivedIso, Localization.Construction.wIso,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    BimoduleCategory.middleRightRestrictionCompIso, BimoduleCategory.middleLeftRestrictionCompIso,
    NatIso.ofComponents_hom_app, bimoduleToDerived, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
