module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.FunctorCoherence

public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtension
public import Mathlib.Data.ZMod.Basic

/-! # 恒等比較の全導来化と指定モデル計算の公理監査

## 概要
恒等比較の全導来化と指定モデル計算の公理監査。

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
universe u v w z
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (L : Type z) [DGCategory A L] [Small.{u} L] (hL : localHomKFlat A L)

example (Q : DerivedBimoduleCategory A D L) (P : DerivedBimoduleCategory A B D) :
    ((derivedMiddleRestrictionNatTrans A B D D L (DGFunctor.id D) hL).app Q).app P =
      ((derivedMiddleIdentityIso A B D L hL).hom.app Q).app P := by
  rw [derivedMiddleRestrictionNatTrans_functor_id]

example (X : Type v) (Y : Type w) (Z : Type z)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y] [DGCategory (ZMod 2) Z]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] (hZ : localHomKFlat (ZMod 2) Z) :
    derivedMiddleRestrictionNatTrans (ZMod 2) X Y Y Z (DGFunctor.id Y) hZ =
      (derivedMiddleIdentityIso (ZMod 2) X Y Z hZ).hom :=
  derivedMiddleRestrictionNatTrans_functor_id (ZMod 2) X Y Z hZ

#print axioms BimoduleTensor.middleClosedIdentityIso
#print axioms BimoduleTensor.middleClosedIdentityIso_hom_app
#print axioms BimoduleTensor.middleIdentitySourceFamilyIso
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalFamily_functor_id
#print axioms BimoduleTensor.middleIdentitySourceLiftIso
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalLocalized_functor_id
#print axioms BimoduleTensor.middleIdentityKFlatIso
#print axioms BimoduleTensor.middleDerivedKFlatComparison_functor_id
#print axioms BimoduleTensor.middleIdentityLocalizedIso
#print axioms BimoduleTensor.middleRightKFlatLocalizedComparison_functor_id
#print axioms BimoduleTensor.middleFullIdentityIso
#print axioms BimoduleTensor.middleFullDerivedComparison_functor_id
#print axioms BimoduleTensor.derivedMiddleIdentityIso
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_functor_id
#print axioms BimoduleTensor.derivedMiddleIdentityIso_transport
#print axioms BimoduleTensor.middleLocalizedRestrictionComparison
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_conjugate
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_precomp_rightKFlat
#print axioms BimoduleTensor.middleLocalizedRestrictionComparison_eq_lift
#print axioms BimoduleTensor.middleLocalizedRestrictionComparison_app
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_app_rightKFlat
#print axioms BimoduleTensor.middleRightKFlatComparison_eq_first_lift
#print axioms BimoduleTensor.derivedMiddleRestrictionNatTrans_app_base
#print axioms bimoduleDerivedIsoOfPrecomp
#print axioms bimoduleDerivedIsoOfPrecomp_hom_app
#print axioms bimoduleDerivedIsoOfPrecomp_inv_app
