module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison
public import Mathlib.Data.ZMod.Basic

/-! # 中間dg圏の制限に沿う全Hom自然なbimodule射と解像度を使う導来比較の検査

## 概要
中間dg圏の制限に沿う全Hom自然なbimodule射と解像度を使う導来比較の検査。

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
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)

-- 終端の対象型のsmallnessなしで、全Hom自然な実際のbimodule射を構成する。
example (P : Bimodule A B C) (Q : Bimodule A C E) :
    BimoduleCategory.of A B E (compose A B D E (Bimodule.leftRestriction A B C D F P)
      (Bimodule.rightRestriction A C D E F Q)) ⟶
        BimoduleCategory.of A B E (compose A B C E P Q) :=
  middleRestrictionComparisonMap A B C D E F P Q

example (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) :
    (BimoduleCategory.valueEvaluation A B E b e).map
      (middleRestrictionComparisonMap A B C D E F P Q) =
        middleRestrictionComparisonValue A B C D E F P Q b e :=
  middleRestrictionComparisonMap_value_eval A B C D E F P Q b e

example (P : Bimodule A B C) (Q : Bimodule A C E) (b : B) (e : E) (d : D)
    {r s n : ℤ} (q : (Q.value (F.obj d) e).X r) (p : (P.value b (F.obj d)).X s)
    (hn : r + s = n) :
    (middleRestrictionComparisonValue A B C D E F P Q b e).f n
      (BalancedTensor.element A D ((Bimodule.rightRestriction A C D E F Q).rightAt e)
        ((Bimodule.leftRestriction A B C D F P).leftAt b) d q p hn) =
      BalancedTensor.element A C (Q.rightAt e) (P.leftAt b) (F.obj d) q p hn :=
  middleRestrictionComparisonValue_element A B C D E F P Q b e d q p hn

-- C・Dの局所Hom-flat性も、制限後の右K-flat性も要求しない。
example [Small.{u} E] (hE : localHomKFlat A E)
    (P : BimoduleCategory A B C) (Q : RightKFlatBimoduleCategory A C E) :
    ((derivedBimoduleComposeFunctor A B D E hE).obj
      ((bimoduleToDerived A D E).obj (BimoduleCategory.of A D E
        (Bimodule.rightRestriction A C D E F (BimoduleCategory.underlying A C E Q.obj))))).obj
      ((bimoduleToDerived A B D).obj (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) ⟶
      ((derivedBimoduleComposeFunctor A B C E hE).obj
        ((bimoduleToDerived A C E).obj Q.obj)).obj ((bimoduleToDerived A B C).obj P) :=
  derivedMiddleRestrictionCanonicalComparison A B C D E F hE P Q

example (X : Type v) (Y : Type w) (Z : Type z) (T : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) T]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z]
    (F : DGFunctor (ZMod 2) Z Y) (P : Bimodule (ZMod 2) X Y)
    (Q : Bimodule (ZMod 2) Y T) :
    BimoduleCategory.of (ZMod 2) X T (compose (ZMod 2) X Z T
      (Bimodule.leftRestriction (ZMod 2) X Y Z F P)
      (Bimodule.rightRestriction (ZMod 2) Y Z T F Q)) ⟶
        BimoduleCategory.of (ZMod 2) X T (compose (ZMod 2) X Y T P Q) :=
  middleRestrictionComparisonMap (ZMod 2) X Y Z T F P Q

namespace SerrePositivity.DifferentialGraded
#print axioms Bimodule.leftRestriction
#print axioms Bimodule.rightRestriction
#print axioms Bimodule.leftRestriction_leftAt
#print axioms Bimodule.rightRestriction_leftAt_map
#print axioms Bimodule.rightRestriction_leftAction
#print axioms BimoduleTensor.middleRestrictionFamily
#print axioms BimoduleTensor.middleRestrictionFamily_val
#print axioms BimoduleTensor.middleRestrictionComparisonValue
#print axioms BimoduleTensor.ι_middleRestrictionComparisonValue
#print axioms BimoduleTensor.middleRestrictionComparisonValue_element
#print axioms BimoduleTensor.middleRestrictionComparisonValue_rightAction
#print axioms BimoduleTensor.middleRestrictionComparisonValue_leftAction
#print axioms BimoduleTensor.middleRestrictionComparisonValue_right_naturality
#print axioms BimoduleTensor.middleRestrictionComparisonValue_left_naturality
#print axioms BimoduleTensor.middleRestrictionComparisonRightMap
#print axioms BimoduleTensor.middleRestrictionComparisonRightMap_eval
#print axioms BimoduleTensor.middleRestrictionComparisonRightMap_component
#print axioms BimoduleTensor.middleRestrictionComparisonRightMap_naturality
#print axioms BimoduleTensor.middleRestrictionComparisonMap
#print axioms BimoduleTensor.middleRestrictionComparisonMap_value_eval
#print axioms BimoduleTensor.middleRestrictionResolvedMap
#print axioms BimoduleTensor.middleRestrictionResolvedMap_comp
#print axioms BimoduleTensor.middleRestrictionSourceComputation
#print axioms BimoduleTensor.derivedMiddleRestrictionComparison
#print axioms BimoduleTensor.derivedMiddleRestrictionCanonicalComparison
end SerrePositivity.DifferentialGraded
