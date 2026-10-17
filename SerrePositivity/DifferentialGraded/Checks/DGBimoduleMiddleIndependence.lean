module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleSemifreeIndependence
public import Mathlib.Data.ZMod.Basic

/-! # 中間圏導来比較の任意の制限後semifree解像度からの独立性の検査

## 概要
中間圏導来比較の任意の制限後semifree解像度からの独立性の検査。

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
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R S : BimoduleSemifreeResolution A D E
    ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))

-- 選んだ二つのsemifree解像度に追加の増大squareを要求しない。
example (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparison A B C D E F hE P Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso :=
  derivedMiddleRestrictionComparison_semifree_independent A B C D E F hE Q R S P

-- 自然変換の等式なので、前因子の全導来圏のすべての射に対する比較を含む。
example : derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (S.toRightKFlat A D E hE) S.π S.quasiIso =
      derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso :=
  derivedMiddleRestrictionComparisonLocalized_semifree_independent A B C D E F hE Q R S

example : derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q
        (R.toRightKFlat A D E hE) R.π R.quasiIso =
      derivedMiddleRestrictionCanonicalLocalized A B C D E F hE Q :=
  derivedMiddleRestrictionComparisonLocalized_semifree_eq_canonical A B C D E F hE Q R

example (X : Type v) (Y : Type w) (Z : Type z) (T : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) T]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} T]
    (F : DGFunctor (ZMod 2) Z Y) (hT : localHomKFlat (ZMod 2) T)
    (Q : RightKFlatBimoduleCategory (ZMod 2) Y T) :
    middleDerivedSourceLift (ZMod 2) X Y Z T F hT Q ⟶
      (derivedBimoduleComposeFunctor (ZMod 2) X Y T hT).obj
        ((bimoduleToDerived (ZMod 2) Y T).obj Q.obj) :=
  derivedMiddleRestrictionCanonicalLocalized (ZMod 2) X Y Z T F hT Q

namespace SerrePositivity.DifferentialGraded
#print axioms bimoduleDerived_map_eq_of_inverse_source_homotopy
#print axioms BimoduleTensor.derivedComposeWithMap_computation
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso
#print axioms BimoduleTensor.derivedBimoduleComposeResolutionValueIso_change
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_eq_of_squares
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_eq_of_source_homotopy
#print axioms BimoduleSemifreeResolution.composeAfter_comparison_fac
#print axioms BimoduleSemifreeResolution.toRightKFlat
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_semifree_independent
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonFamily_semifree_independent
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonLocalized_semifree_independent
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison_semifree_eq_canonical
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalLocalized
#print axioms BimoduleTensor.derivedMiddleRestrictionComparisonLocalized_semifree_eq_canonical
end SerrePositivity.DifferentialGraded
