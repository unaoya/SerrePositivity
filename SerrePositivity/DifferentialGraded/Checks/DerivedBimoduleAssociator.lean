module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Resolution
public import Mathlib.Data.ZMod.Basic

/-! # 全三因子に自然な導来結合比較と局所化前の計算式の監査

## 概要
全三因子に自然な導来結合比較と局所化前の計算式の監査。

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

example (hE : localHomKFlat A E) (hF : localHomKFlat A F) :
    derivedBimoduleAssociatorSource A B C E F hE hF ≅
      derivedBimoduleAssociatorTarget A B C E F hF :=
  derivedBimoduleAssociatorIso A B C E F hE hF

-- 最後の因子の任意の導来射。
example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    {R R' : DerivedBimoduleCategory A E F} (g : R ⟶ R') :
    (derivedBimoduleAssociatorSource A B C E F hE hF).map g ≫
        (derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R' =
      (derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R ≫
        (derivedBimoduleAssociatorTarget A B C E F hF).map g :=
  (derivedBimoduleAssociatorIso A B C E F hE hF).hom.naturality g

-- 中間因子の任意の導来射。
example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (R : DerivedBimoduleCategory A E F) {Q Q' : DerivedBimoduleCategory A C E} (f : Q ⟶ Q') :
    ((derivedBimoduleAssociatorSource A B C E F hE hF).obj R).map f ≫
        ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).app Q' =
      ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).app Q ≫
        ((derivedBimoduleAssociatorTarget A B C E F hF).obj R).map f :=
  ((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).naturality f

-- 最初の因子の任意の導来射。
example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (R : DerivedBimoduleCategory A E F) (Q : DerivedBimoduleCategory A C E)
    {P P' : DerivedBimoduleCategory A B C} (f : P ⟶ P') :
    (((derivedBimoduleAssociatorSource A B C E F hE hF).obj R).obj Q).map f ≫
        (((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).app Q).app P' =
      (((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).app Q).app P ≫
        (((derivedBimoduleAssociatorTarget A B C E F hF).obj R).obj Q).map f :=
  (((derivedBimoduleAssociatorIso A B C E F hE hF).hom.app R).app Q).naturality f

example (hE : localHomKFlat A E) (hF : localHomKFlat A F)
    (Q : BimoduleCategory A C E) (R : BimoduleCategory A E F) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
      ((bimoduleToDerived A E F).obj R)).app ((bimoduleToDerived A C E).obj Q)).hom =
      (derivedBimoduleAssociatorBaseIso A B C E F hE hF Q R).hom :=
  derivedBimoduleAssociatorIso_base_app A B C E F hE hF Q R

example (B : Type v) (C : Type w) (E : Type z) (F : Type t)
    [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [DGCategory (ZMod 2) E] [DGCategory (ZMod 2) F]
    [Small.{0} B] [Small.{0} C] [Small.{0} E] [Small.{0} F]
    (hE : localHomKFlat (ZMod 2) E) (hF : localHomKFlat (ZMod 2) F) :
    derivedBimoduleAssociatorSource (ZMod 2) B C E F hE hF ≅
      derivedBimoduleAssociatorTarget (ZMod 2) B C E F hF :=
  derivedBimoduleAssociatorIso (ZMod 2) B C E F hE hF

#print axioms derivedBimoduleComposePairMap
#print axioms derivedBimoduleComposePairResolutionIso_naturality
#print axioms derivedBimoduleComposeInnerMap
#print axioms derivedBimoduleComposeInnerResolutionIso_naturality
#print axioms derivedBimoduleComposeNestedResolutionIso_naturality
#print axioms derivedBimoduleAssociatorResolutionIso_naturality
#print axioms derivedBimoduleAssociatorBaseIso_naturality
#print axioms derivedBimoduleAssociatorSource
#print axioms derivedBimoduleAssociatorTarget
#print axioms derivedBimoduleAssociatorMiddleBaseIso
#print axioms derivedBimoduleAssociatorMiddleIso
#print axioms derivedBimoduleAssociatorMiddleIso_base_app
#print axioms derivedBimoduleAssociatorMiddleIso_naturality
#print axioms derivedBimoduleAssociatorOuterBaseIso
#print axioms derivedBimoduleAssociatorIso
#print axioms derivedBimoduleAssociatorIso_outer_base_app
#print axioms derivedBimoduleAssociatorIso_base_app
