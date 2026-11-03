module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels

public import Mathlib.Data.ZMod.Basic

/-! # 二段階sourceの正規化squareと移送付き全導来比較の検査

## 概要
二段階sourceの正規化squareと移送付き全導来比較の検査。

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
universe u v w z t s
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

-- 中間圏の局所Hom K-flat性とF・Gの準同値性なしの、実際のsource square。
example (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T) :
    (middleIteratedClosedSourceIso A B D E T L F G hL Q P).hom ≫
        ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app
          ((bimoduleToDerived A T L).obj Q)).app ((bimoduleToDerived A B T).obj P) =
      (middleIteratedClosedNormalizationIso A B D E T L F G hL Q P).hom ≫
        ((middleClosedSourceIdentification A B T D L (F.comp G) hL).hom.app Q).app P :=
  middleIteratedClosedSourceIso_normalize A B D E T L F G hL Q P

-- 移送する導来射には可逆性を課さない。
example (Q : RightKFlatBimoduleCategory A E L) (P : BimoduleCategory A B E)
    (Q' : DerivedBimoduleCategory A E L) (P' : DerivedBimoduleCategory A B E)
    (g : (bimoduleToDerived A E L).obj Q.obj ⟶ Q')
    (f : (bimoduleToDerived A B E).obj P ⟶ P') :
    (middleDerivedSourceFamilyIdentification A B E D L F hL Q).hom.app P ≫
        ((middleRestrictionDerivedSource A B E D L F hL).map g).app
          ((bimoduleToDerived A B E).obj P) ≫
        ((middleRestrictionDerivedSource A B E D L F hL).obj Q').map f ≫
        ((derivedMiddleRestrictionNatTrans A B E D L F hL).app Q').app P' =
      derivedMiddleRestrictionCanonicalComparison A B E D L F hL P Q ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map g).app
          ((bimoduleToDerived A B E).obj P) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).obj Q').map f :=
  derivedMiddleRestrictionNatTrans_transport_fac A B E D L F hL Q P Q' P' g f

example (X : Type v) (Y : Type w) (Z : Type z)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y] [DGCategory (ZMod 2) Z]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z]
    (F' : DGFunctor (ZMod 2) X Y) (G' : DGFunctor (ZMod 2) Y Z) :
    (middleRightIteratedDerivedIso (ZMod 2) X X Y Z F' G').hom ≫
        Functor.whiskerLeft (bimoduleToDerived (ZMod 2) Z X)
          (middleRightDerivedCompIso (ZMod 2) X X Y Z F' G').hom =
      Functor.whiskerRight
          (BimoduleCategory.middleRightRestrictionCompIso (ZMod 2) X X Y Z F' G').hom
          (bimoduleToDerived (ZMod 2) X X) ≫
        (middleRightRestrictionDerivedIso (ZMod 2) Z X (F'.comp G') X).hom :=
  middleRightIteratedDerivedIso_normalize (ZMod 2) X X Y Z F' G'

#print axioms middleLeftIteratedDerivedIso
#print axioms middleLeftIteratedDerivedIso_normalize
#print axioms middleRightIteratedDerivedIso
#print axioms middleRightIteratedDerivedIso_normalize
#print axioms BimoduleTensor.middleIteratedClosedSourceIso
#print axioms BimoduleTensor.middleIteratedClosedNormalizationIso
#print axioms BimoduleTensor.middleIteratedClosedSourceIso_normalize
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_base_fac
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_transport_fac
