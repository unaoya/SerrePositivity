module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorResolution
public import Mathlib.Data.ZMod.Basic

/-! # 指定K-flat解像度による全導来結合比較の監査

## 概要
指定K-flat解像度による全導来結合比較の監査。

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
universe u v w z t
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q) ⋙
        (derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R) ≅
      (derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q)) :=
  derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R

-- 前因子は局所化前の射に限らず、全導来圏の任意の射でよい。
example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F)
    (q : S.obj ⟶ Q) (r : T.obj ⟶ R)
    (hq : BimoduleCategory.quasiIso A C E q) (hr : BimoduleCategory.quasiIso A E F r)
    {P P' : DerivedBimoduleCategory A B C} (f : P ⟶ P') :
    ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj R)).map
        (((derivedBimoduleComposeFunctor A B C E hE).obj
          ((bimoduleToDerived A C E).obj Q)).map f) ≫
      (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom.app P' =
    (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom.app P ≫
      ((derivedBimoduleComposeFunctor A B C F hF).obj
        (((derivedBimoduleComposeFunctor A C E F hF).obj
          ((bimoduleToDerived A E F).obj R)).obj ((bimoduleToDerived A C E).obj Q))).map f :=
  (derivedBimoduleAssociatorResolutionIso A B C E F hE hF Q R S T q r hq hr).hom.naturality f

example (B : Type v) (C : Type w) (E : Type z) (F : Type t)
    [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [DGCategory (ZMod 2) E] [DGCategory (ZMod 2) F]
    [Small.{0} B] [Small.{0} C] [Small.{0} E] [Small.{0} F]
    (hE : localHomKFlat (ZMod 2) E) (hF : localHomKFlat (ZMod 2) F)
    (Q : BimoduleCategory (ZMod 2) C E) (R : BimoduleCategory (ZMod 2) E F) :
    (derivedBimoduleComposeFunctor (ZMod 2) B C E hE).obj
        ((bimoduleToDerived (ZMod 2) C E).obj Q) ⋙
      (derivedBimoduleComposeFunctor (ZMod 2) B E F hF).obj
        ((bimoduleToDerived (ZMod 2) E F).obj R) ≅
    (derivedBimoduleComposeFunctor (ZMod 2) B C F hF).obj
      (((derivedBimoduleComposeFunctor (ZMod 2) C E F hF).obj
        ((bimoduleToDerived (ZMod 2) E F).obj R)).obj
          ((bimoduleToDerived (ZMod 2) C E).obj Q)) :=
  derivedBimoduleAssociatorBaseIso (ZMod 2) B C E F hE hF Q R

#print axioms derivedBimoduleComposePairResolutionIso
#print axioms derivedBimoduleComposeInnerResolutionIso
#print axioms derivedBimoduleComposeNestedResolutionIso
#print axioms derivedBimoduleAssociatorResolutionIso
#print axioms derivedBimoduleAssociatorResolutionIso_fac
#print axioms derivedBimoduleAssociatorResolutionIso_base_fac
#print axioms derivedBimoduleAssociatorBaseIso
