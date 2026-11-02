module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels
public import SerrePositivity.DifferentialGraded.Derived.LeftUnit
public import Mathlib.Data.ZMod.Basic

/-! # 外側・中間の全導来比較の任意モデル計算と左単位経路の検査

## 概要
外側・中間の全導来比較の任意モデル計算と左単位経路の検査。

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
universe u v w z t s
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section Models
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

-- F・Gの準同値性や、B・C・D・Kのlocal Hom条件を要求しない。
example :
    restrictedMiddleModelPrefix A B C D E F K G hE P Q R q hq ≫
      (derivedBimoduleRestriction A K E B E G (DGFunctor.id E)).map
        ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
          ((derivedMiddleRestrictionNatTrans A B C D E F hE).app
            ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
          (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom) =
    (bimoduleToDerived A K E).map
        (composeRightRestrictionIso A B K D E G
          ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P) R.obj).hom ≫
      (bimoduleToDerived A K E).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B K E G).map
          (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) ≫
      (middleRightRestrictionDerivedIso A B K G E).hom.app
        ((composeWith A B C E Q.obj).obj P) :=
  derivedBimoduleRestriction_model_calculation A B C D E F K G hE P Q R q hq
end Models

-- 標数2・任意の導来射でも、実際の比較で構成した左単位経路は自然。
theorem SerrePositivity.DifferentialGraded.Checks.leftUnitRestrictionPath_charTwo_naturality
    (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] [Small.{0} C]
    (F : DGFunctor (ZMod 2) D B) (hC : localHomKFlat (ZMod 2) C)
    {Q Q' : DerivedBimoduleCategory (ZMod 2) B C} (f : Q ⟶ Q') :
    (derivedBimoduleRestriction (ZMod 2) D C B C F (DGFunctor.id C) ⋙
        derivedBimoduleLeftUnitFunctor (ZMod 2) D C hC).map f ≫
      (leftUnitRestrictionDerivedComparison (ZMod 2) B D C F hC).app Q' =
    (leftUnitRestrictionDerivedComparison (ZMod 2) B D C F hC).app Q ≫
      (derivedBimoduleRestriction (ZMod 2) D C B C F (DGFunctor.id C)).map f :=
  (leftUnitRestrictionDerivedComparison (ZMod 2) B D C F hC).naturality f

#print axioms derivedMiddleRestrictionComparison_output_restriction
#print axioms derivedMiddleRestrictionComparison_output_restriction_expanded
#print axioms rightKFlatComposePresentationIso_hom_app
#print axioms derivedBimoduleComposeRightRestrictionIso_resolution_square
#print axioms derivedBimoduleComposeRightRestrictionIso_resolution_app_calc
#print axioms middleDerivedSourceFamilyIdentification_hom_app_calc
#print axioms derivedMiddleRestrictionNatTrans_resolution_calculation
#print axioms derivedMiddleRestrictionNatTrans_resolution_output_restriction
#print axioms restrictedMiddleModelPrefix
#print axioms derivedBimoduleRestriction_model_calculation
#print axioms leftUnitRestrictionDerivedDiagonalMap
#print axioms leftUnitRestrictionDerivedComparison
#print axioms leftUnitRestrictionDerivedComparison_app
#print axioms SerrePositivity.DifferentialGraded.Checks.leftUnitRestrictionPath_charTwo_naturality
