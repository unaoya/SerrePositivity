module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullComparison
public import Mathlib.Data.ZMod.Basic

/-! # 中間圏比較の両変数の全導来圏上での自然性と局所化の検査

## 概要
中間圏比較の両変数の全導来圏上での自然性と局所化の検査。

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
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E)

-- C・Dの局所Hom-flat性も、制限後のK-flat性も要求せず、全導来圏上に構成する。
example : middleFullDerivedSource A B C D E F hE ⟶ derivedBimoduleComposeFunctor A B C E hE :=
  middleFullDerivedComparison A B C D E F hE

-- 後因子は任意の導来対象と任意の導来射でよい。
example {Q Q' : DerivedBimoduleCategory A C E} (g : Q ⟶ Q') :
    (middleFullDerivedSource A B C D E F hE).map g ≫
        (middleFullDerivedComparison A B C D E F hE).app Q' =
      (middleFullDerivedComparison A B C D E F hE).app Q ≫
        (derivedBimoduleComposeFunctor A B C E hE).map g :=
  (middleFullDerivedComparison A B C D E F hE).naturality g

-- 前因子も同じ全導来圏上の任意の射に関して自然。
example (Q : DerivedBimoduleCategory A C E) {P P' : DerivedBimoduleCategory A B C} (f : P ⟶ P') :
    ((middleFullDerivedSource A B C D E F hE).obj Q).map f ≫
        ((middleFullDerivedComparison A B C D E F hE).app Q).app P' =
      ((middleFullDerivedComparison A B C D E F hE).app Q).app P ≫
        ((derivedBimoduleComposeFunctor A B C E hE).obj Q).map f :=
  ((middleFullDerivedComparison A B C D E F hE).app Q).naturality f

example (X : Type v) (Y : Type w) (Z : Type z) (T : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) T]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} T]
    (F : DGFunctor (ZMod 2) Z Y) (hT : localHomKFlat (ZMod 2) T) :
    middleFullDerivedSource (ZMod 2) X Y Z T F hT ⟶
      derivedBimoduleComposeFunctor (ZMod 2) X Y T hT :=
  middleFullDerivedComparison (ZMod 2) X Y Z T F hT

namespace SerrePositivity.DifferentialGraded
#print axioms BimoduleSemifreeResolution.lift
#print axioms BimoduleSemifreeResolution.lift_fac
#print axioms BimoduleSemifreeResolution.composeAfter_lift_fac
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso_naturality
#print axioms BimoduleTensor.derivedBimoduleComposeKFlatValueIso_naturality
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_second_naturality_of_squares
#print axioms BimoduleTensor.middleRestrictionResolvedMap_semifree_second_naturality
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_semifree_second_naturality
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalComparison_second_naturality
#print axioms BimoduleTensor.middleDerivedSourceFamilyMap
#print axioms BimoduleTensor.middleDerivedTargetFamilyMap
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalFamily
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalFamily_app
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalFamily_second_naturality
#print axioms BimoduleTensor.middleDerivedSourceLiftMap
#print axioms BimoduleTensor.middleDerivedTargetFamilyMap_lift
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalFamily_lift
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalLocalized_second_naturality
#print axioms BimoduleTensor.middleDerivedSourceFamilyMap_id
#print axioms BimoduleTensor.middleDerivedSourceFamilyMap_comp
#print axioms BimoduleTensor.middleDerivedSourceLiftMap_id
#print axioms BimoduleTensor.middleDerivedSourceLiftMap_comp
#print axioms BimoduleTensor.middleDerivedSourceKFlatFunctor
#print axioms BimoduleTensor.middleDerivedTargetKFlatFunctor
#print axioms BimoduleTensor.middleDerivedKFlatComparison
#print axioms BimoduleTensor.middleDerivedSourceKFlatFunctor_inverts
#print axioms BimoduleTensor.middleRightKFlatLocalizedSource
#print axioms BimoduleTensor.middleRightKFlatLocalizedSource_fac
#print axioms BimoduleTensor.middleRightKFlatLocalizedSource_lifting
#print axioms BimoduleTensor.middleRightKFlatLocalizedTarget_fac
#print axioms BimoduleTensor.middleRightKFlatLocalizedTarget_lifting
#print axioms BimoduleTensor.middleRightKFlatLocalizedComparison
#print axioms BimoduleTensor.middleRightKFlatLocalizedComparison_app
#print axioms BimoduleTensor.middleFullDerivedSource
#print axioms BimoduleTensor.middleFullDerivedTargetIso
#print axioms BimoduleTensor.middleFullDerivedComparison
#print axioms BimoduleTensor.middleFullDerivedComparison_app
end SerrePositivity.DifferentialGraded
