module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFull
public import Mathlib.Data.ZMod.Basic

/-! # 外側左制限の全導来合成比較と必要仮定の検査

## 概要
外側左制限の全導来合成比較と必要仮定の検査。

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
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)

-- 固定K-flat後因子の比較にはE・D・Cの局所Hom K-flat性もFの準同値性も不要。
example (Q : RightKFlatBimoduleCategory A C E) :
    derivedComposeWith A B C D ((rightKFlatLeftRestriction A C E D F).obj Q).obj
        ((rightKFlatLeftRestriction A C E D F).obj Q).property ≅
      derivedComposeWith A B C E Q.obj Q.property ⋙
        derivedBimoduleRestriction A B D B E (DGFunctor.id B) F :=
  derivedComposeWithLeftRestrictionIso A B C E D F Q

-- 両変数とも任意の導来対象。Fの準同値性とCの局所Hom K-flat性は要求しない。
example (hE : localHomKFlat A E) (hD : localHomKFlat A D)
    (Q : DerivedBimoduleCategory A C E) (P : DerivedBimoduleCategory A B C) :
    (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).obj
        (((derivedBimoduleComposeFunctor A B C E hE).obj Q).obj P) ≅
      ((derivedBimoduleComposeFunctor A B C D hD).obj
        ((derivedBimoduleRestriction A C D C E (DGFunctor.id C) F).obj Q)).obj P :=
  ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).app Q).app P

-- 後因子の任意の閉零射に関する自然性。準同型性を課さない。
example {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q') :
    (leftRestrictionKFlatComposeSource A B C E D F).map g ≫
        (derivedComposeWithLeftRestrictionIso A B C E D F Q').hom =
      (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom ≫
        (leftRestrictionKFlatComposeTarget A B C E D F).map g :=
  derivedComposeWithLeftRestrictionIso_naturality A B C E D F g

example (X : Type v) (Y : Type w) (Z : Type z) (W : Type t)
    [DGCategory (ZMod 2) X] [DGCategory (ZMod 2) Y]
    [DGCategory (ZMod 2) Z] [DGCategory (ZMod 2) W]
    [Small.{0} X] [Small.{0} Y] [Small.{0} Z] [Small.{0} W]
    (F' : DGFunctor (ZMod 2) W Z) (hZ : localHomKFlat (ZMod 2) Z)
    (hW : localHomKFlat (ZMod 2) W) :
    leftRestrictionDerivedComposeSource (ZMod 2) X Y Z W F' hZ ≅
      leftRestrictionDerivedComposeTarget (ZMod 2) X Y Z W F' hW :=
  derivedBimoduleComposeLeftRestrictionIso (ZMod 2) X Y Z W F' hZ hW

#print axioms BimoduleTensor.compose_leftRestriction
#print axioms BimoduleTensor.composeLeftRestrictionIso
#print axioms BimoduleTensor.composeLeftRestrictionIso_hom_value
#print axioms BimoduleTensor.composeLeftRestrictionIso_naturality
#print axioms BimoduleTensor.leftRestriction_rightRelativeKFlat
#print axioms BimoduleTensor.leftRestriction_quasiIso
#print axioms BimoduleTensor.rightKFlatLeftRestriction
#print axioms BimoduleTensor.rightKFlatLeftRestriction_fac
#print axioms BimoduleTensor.rightKFlatLeftRestriction_quasiIso
#print axioms BimoduleTensor.composeWithLeftRestrictionIso
#print axioms BimoduleTensor.composeWithLeftRestrictionIso_naturality
#print axioms BimoduleTensor.composeWithLeftRestrictionLocalizedIso
#print axioms BimoduleTensor.derivedComposeWithLeftRestrictionPreIso
#print axioms BimoduleTensor.derivedComposeWithLeftRestrictionIso
#print axioms BimoduleTensor.derivedComposeWithLeftRestrictionIso_hom_app
#print axioms BimoduleTensor.derivedComposeWithLeftRestrictionIso_hom_app_calc
#print axioms BimoduleTensor.leftRestrictionKFlatComposeSource
#print axioms BimoduleTensor.leftRestrictionKFlatComposeTarget
#print axioms BimoduleTensor.derivedComposeWithLeftRestrictionIso_naturality
#print axioms BimoduleTensor.leftRestrictionKFlatComposeIso
#print axioms BimoduleTensor.rightKFlatDerivedIsoOfPrecomp
#print axioms BimoduleTensor.rightKFlatComposePresentationIso
#print axioms BimoduleTensor.leftRestrictionDerivedComposeSource
#print axioms BimoduleTensor.leftRestrictionDerivedComposeTarget
#print axioms BimoduleTensor.leftRestrictionDerivedComposeSourceBaseIso
#print axioms BimoduleTensor.leftRestrictionDerivedComposeTargetBaseIso
#print axioms BimoduleTensor.derivedBimoduleComposeLeftRestrictionIso
