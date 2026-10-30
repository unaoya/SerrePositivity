module
public import SerrePositivity.DifferentialGraded.Resolution.MiddleCompositionComparison
public import Mathlib.Data.ZMod.Basic

/-! # 中間圏比較の全導来合成則とdg圏解像度比較への適用の検査

## 概要
中間圏比較の全導来合成則とdg圏解像度比較への適用の検査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t s w'
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

-- 両変数とも任意の導来対象。中間圏の局所Hom K-flat性とF・Gの準同値性は不要。
example (Q : DerivedBimoduleCategory A T L) (P : DerivedBimoduleCategory A B T) :
    ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app Q).app P ≫
        ((derivedMiddleRestrictionNatTrans A B T D L (F.comp G) hL).app Q).app P =
      ((derivedMiddleRestrictionNatTrans A B E D L F hL).app
          ((derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj Q)).app
          ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj P) ≫
        ((derivedMiddleRestrictionNatTrans A B T E L G hL).app Q).app P :=
  derivedMiddleRestrictionNatTrans_functor_comp_app A B D E T L F G hL Q P

example (hF : QuasiEquivalence F) (hG : QuasiEquivalence G) :
    middleIteratedDerivedSourceIso A B D E T L F G hL ≪≫
        derivedMiddleRestrictionIso A B T D L (F.comp G)
          (quasiEquivalence_comp F G hF hG) hL =
      middleIteratedDerivedIso A B D E T L F G hL hF hG :=
  derivedMiddleRestrictionIso_functor_comp A B D E T L F G hL hF hG

-- 元のtarget Xのsmallness・局所Hom K-flat性を追加しない。
example (X : Type t) [DGCategory A X] (R : KFlatDGResolution.{u, t, w'} A X) :
    middleRestrictionDerivedSource A B R.source R.ComparisonSource L R.comparisonLeft hL ≅
      derivedBimoduleComposeFunctor A B R.source L hL :=
  ResolutionBimodule.middleComparisonLeftIso A B L hL R

example (X : Type t) [DGCategory A X] [Small.{u} X]
    (R : KFlatDGResolution.{u, t, w'} A X) :
    middleRestrictionDerivedSource A B (KFlatDGResolution.canonical A X).source
        R.ComparisonSource L R.comparisonRight hL ≅
      derivedBimoduleComposeFunctor A B (KFlatDGResolution.canonical A X).source L hL :=
  ResolutionBimodule.middleComparisonRightIso A B L hL R

example (X : Type v) (Y : Type w) (Z : Type z) (W : Type t) (V : Type s)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y] [DGCategory (ZMod 2) Z]
    [DGCategory (ZMod 2) W] [DGCategory (ZMod 2) V]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} W] [Small.{0} V]
    (F' : DGFunctor (ZMod 2) Y Z) (G' : DGFunctor (ZMod 2) Z W)
    (hV : localHomKFlat (ZMod 2) V) :
    (middleIteratedDerivedSourceIso (ZMod 2) X Y Z W V F' G' hV).hom ≫
        derivedMiddleRestrictionNatTrans (ZMod 2) X W Y V (F'.comp G') hV =
      middleIteratedDerivedComparison (ZMod 2) X Y Z W V F' G' hV :=
  derivedMiddleRestrictionNatTrans_functor_comp (ZMod 2) X Y Z W V F' G' hV

#print axioms BimoduleTensor.middleIteratedAugmentedSourceMap
#print axioms BimoduleTensor.middleIteratedAugmentedSourceMap_normalize
#print axioms BimoduleTensor.middleIteratedAugmentedSourceMap_transport
#print axioms BimoduleTensor.middleIteratedAugmentedComparison_fac
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_functor_comp
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_functor_comp_app
#print axioms BimoduleTensor.middleIteratedDerivedIso
#print axioms BimoduleTensor.derivedMiddleRestrictionIso_functor_comp
#print axioms ResolutionBimodule.middleComparisonLeftIso
#print axioms ResolutionBimodule.middleComparisonLeftIso_refine
#print axioms ResolutionBimodule.middleComparisonRightIso
#print axioms ResolutionBimodule.middleComparisonRightIso_refine
