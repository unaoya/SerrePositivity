module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFull
public import Mathlib.Data.ZMod.Basic

/-! # 外側右制限の全Hom比較・全導来合成・必要仮定の検査

## 概要
外側右制限の全Hom比較・全導来合成・必要仮定の検査。

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
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)

-- 左加群の対象の等式には、左作用のdg圏のsmallnessを追加しない。
example (X : Type z) [DGCategory A X] (P : Bimodule A B X) (d : D) :
    (Bimodule.rightRestriction A B D X F P).leftAt d = P.leftAt (F.obj d) :=
  Bimodule.rightRestriction_leftAt_eq A B D X F P d

-- 全Hom複体での右作用自然性。閉零射だけへの弱化ではない。
example (P : Bimodule A B C) (Q : Bimodule A C E) (d d' : Dᵒᵖ) (e : E) :
    ((compose A D C E (Bimodule.rightRestriction A B D C F P) Q).rightAt e).map d d' ≫
        homPostcompose _ (composeRightRestrictionValueIso A B D C E F P Q d'.unop e).hom =
      ((Bimodule.rightRestriction A B D E F (compose A B C E P Q)).rightAt e).map d d' ≫
        homPrecompose (composeRightRestrictionValueIso A B D C E F P Q d.unop e).hom _ :=
  composeRightRestrictionValueIso_right_naturality A B D C E F P Q d d' e

-- 固定モデル版には、どのdg圏にもlocal Hom K-flat性を要求しない。
example (Q : RightKFlatBimoduleCategory A C E) :
    derivedBimoduleRestriction A D C B C F (DGFunctor.id C) ⋙
        derivedComposeWith A D C E Q.obj Q.property ≅
      derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A D E B E F (DGFunctor.id E) :=
  derivedComposeWithRightRestrictionIso A B D C E F Q

-- 両変数とも任意の導来対象。Fの準同値性やB・D・Cのlocal Hom条件は不要。
example (hE : localHomKFlat A E)
    (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeFunctor A D C E hE).obj Q).obj
        ((derivedBimoduleRestriction A D C B C F (DGFunctor.id C)).obj P) ≅
      (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).obj
        (((derivedBimoduleComposeFunctor A B C E hE).obj Q).obj P) :=
  ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).app Q).app P

example (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
    (P : DerivedBimoduleCategory A B C) :
    ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q.obj)).app P ≫
        ((rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q).app P =
      ((rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q).app P ≫
        (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app P :=
  NatTrans.congr_app (derivedBimoduleComposeRightRestrictionIso_model_square
    A B D C E F hE Q) P

example (X : Type v) (Y : Type w) (Z : Type z) (W : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) W]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} W]
    (F' : DGFunctor (ZMod 2) Y X) (hW : localHomKFlat (ZMod 2) W) :
    rightRestrictionDerivedComposeSource (ZMod 2) X Y Z W F' hW ≅
      rightRestrictionDerivedComposeTarget (ZMod 2) X Y Z W F' hW :=
  derivedBimoduleComposeRightRestrictionIso (ZMod 2) X Y Z W F' hW

#print axioms Bimodule.rightRestriction_leftAt_eq
#print axioms Bimodule.rightRestrictionLeftEvaluationIso
#print axioms Bimodule.rightRestrictionLeftEvaluationIso_hom_eval
#print axioms Bimodule.rightRestrictionLeftEvaluationIso_inv_eval
#print axioms BimoduleTensor.composeRightRestrictionValueIso
#print axioms BimoduleTensor.ι_composeRightRestrictionValueIso_hom
#print axioms BimoduleTensor.composeRightRestrictionValueIso_element
#print axioms BimoduleTensor.composeRightRestrictionValueIso_rightAction
#print axioms BimoduleTensor.composeRightRestrictionValueIso_leftAction
#print axioms BimoduleTensor.composeRightRestrictionValueIso_right_naturality
#print axioms BimoduleTensor.composeRightRestrictionValueIso_left_naturality
#print axioms BimoduleTensor.composeRightRestrictionRightIso
#print axioms BimoduleTensor.composeRightRestrictionIso
#print axioms BimoduleTensor.composeRightRestrictionIso_hom_value
#print axioms BimoduleTensor.composeRightRestrictionIso_inv_value
#print axioms BimoduleTensor.composeRightRestrictionIso_naturality
#print axioms BimoduleTensor.composeWithRightRestrictionIso
#print axioms BimoduleTensor.composeWithRightRestrictionIso_naturality
#print axioms BimoduleTensor.composeWithRightRestrictionLocalizedIso
#print axioms BimoduleTensor.derivedComposeWithRightRestrictionPreIso
#print axioms BimoduleTensor.derivedComposeWithRightRestrictionIso
#print axioms BimoduleTensor.derivedComposeWithRightRestrictionIso_hom_app
#print axioms BimoduleTensor.derivedComposeWithRightRestrictionIso_hom_app_calc
#print axioms BimoduleTensor.rightRestrictionKFlatComposeSource
#print axioms BimoduleTensor.rightRestrictionKFlatComposeTarget
#print axioms BimoduleTensor.derivedComposeWithRightRestrictionIso_naturality
#print axioms BimoduleTensor.rightRestrictionKFlatComposeIso
#print axioms BimoduleTensor.rightRestrictionDerivedComposeSource
#print axioms BimoduleTensor.rightRestrictionDerivedComposeTarget
#print axioms BimoduleTensor.rightRestrictionDerivedComposeSourceBaseIso
#print axioms BimoduleTensor.rightRestrictionDerivedComposeTargetBaseIso
#print axioms BimoduleTensor.derivedBimoduleComposeRightRestrictionIso
#print axioms BimoduleTensor.derivedBimoduleComposeRightRestrictionIso_app_rightKFlat
#print axioms BimoduleTensor.derivedBimoduleComposeRightRestrictionIso_model_square
#print axioms BimoduleTensor.derivedBimoduleComposeRightRestriction_hom_unique
