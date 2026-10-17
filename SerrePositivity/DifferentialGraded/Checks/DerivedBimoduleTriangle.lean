module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionTriangleFamily
public import Mathlib.Data.ZMod.Basic

/-! # 全導来bimodule合成の三角恒等式の監査

## 概要
全導来bimodule合成の三角恒等式の監査。

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
universe u v w z
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E]
  [Small.{u} B] [Small.{u} C] [Small.{u} E]

example (hC : localHomKFlat A C) (hE : localHomKFlat A E) :
    derivedBimoduleTriangleLeft A B C E hC hE =
      derivedBimoduleTriangleRight A B C E hC hE :=
  derivedBimoduleTriangle A B C E hC hE

-- 後因子・前因子のいずれも局所化前の対象やK-flat対象に限定しない。
example (hC : localHomKFlat A C) (hE : localHomKFlat A E)
    (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((((derivedBimoduleAssociatorIso A B C C E hC hE).app Q).app
        ((bimoduleToDerived A C C).obj (rightKFlatDiagonal A C).obj)).hom.app P) ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map
        ((derivedBimoduleLeftUnitIso A C E hE).hom.app Q)).app P =
    ((derivedBimoduleComposeFunctor A B C E hE).obj Q).map
      ((derivedBimoduleRightUnitIso A B C hC).hom.app P) :=
  NatTrans.congr_app (derivedBimoduleTriangle_app A B C E hC hE Q) P

example (B : Type v) (C : Type w) (E : Type z)
    [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C] [DGCategory (ZMod 2) E]
    [Small.{0} B] [Small.{0} C] [Small.{0} E]
    (hC : localHomKFlat (ZMod 2) C) (hE : localHomKFlat (ZMod 2) E) :
    derivedBimoduleTriangleLeft (ZMod 2) B C E hC hE =
      derivedBimoduleTriangleRight (ZMod 2) B C E hC hE :=
  derivedBimoduleTriangle (ZMod 2) B C E hC hE

#print axioms derivedBimoduleTriangle_kFlat
#print axioms derivedBimoduleTriangleSource
#print axioms derivedBimoduleTriangleLeft
#print axioms derivedBimoduleTriangleRight
#print axioms derivedBimoduleTriangleFamily_kFlat
#print axioms derivedBimoduleTriangle
#print axioms derivedBimoduleTriangle_app
