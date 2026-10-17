module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensorPentagon
public import Mathlib.Data.ZMod.Basic

/-! # 右K-flat固定因子に関する導来五角整合性の受入監査

## 概要
右K-flat固定因子に関する導来五角整合性の受入監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w z t x
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

-- Gのsmall性も各HomのA-flat性も、この五角の追加仮定ではない。
example (Q : RightKFlatBimoduleCategory A C E)
    (R : RightKFlatBimoduleCategory A E F) (S : RightKFlatBimoduleCategory A F G) :
    whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatDerivedAssociator A B E F G R S).hom ≫
      (rightKFlatDerivedAssociator A B C E G Q (rightKFlatCompose A E F G R S)).hom =
    whiskerRight (rightKFlatDerivedAssociator A B C E F Q R).hom
        (rightKFlatDerivedCompose A B F G S) ≫
      (rightKFlatDerivedAssociator A B C F G (rightKFlatCompose A C E F Q R) S).hom ≫
      rightKFlatDerivedMap A B C G
        (Q := rightKFlatCompose A C F G (rightKFlatCompose A C E F Q R) S)
        (Q' := rightKFlatCompose A C E G Q (rightKFlatCompose A E F G R S))
        (associatorIso A C E F G (BimoduleCategory.underlying A C E Q.obj)
          (BimoduleCategory.underlying A E F R.obj) (BimoduleCategory.underlying A F G S.obj)).hom
      :=
  derivedPentagon A B C E F G Q R S

example (B : Type v) (C : Type w) (E : Type z) (F : Type t) (G : Type x)
    [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C] [DGCategory (ZMod 2) E]
    [DGCategory (ZMod 2) F] [DGCategory (ZMod 2) G]
    [Small.{0} B] [Small.{0} C] [Small.{0} E] [Small.{0} F]
    (Q : RightKFlatBimoduleCategory (ZMod 2) C E)
    (R : RightKFlatBimoduleCategory (ZMod 2) E F)
    (S : RightKFlatBimoduleCategory (ZMod 2) F G) :=
  derivedPentagon (ZMod 2) B C E F G Q R S

#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightKFlatCompose
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightKFlatDerivedCompose
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightKFlatDerivedMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightKFlatDerivedAssociator
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightKFlatDerivedCompose_map_base
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightKFlatDerivedMap_base_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.rightKFlatDerivedAssociator_base_app
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensor.derivedPentagon
