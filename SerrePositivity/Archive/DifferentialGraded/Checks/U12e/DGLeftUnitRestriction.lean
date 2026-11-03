module
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence
public import Mathlib.Data.ZMod.Basic

/-! # 左単位子と対角・中間・外側制限比較のモデルsquareの検査

## 概要
左単位子と対角・中間・外側制限比較のモデルsquareの検査。

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
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BimoduleTensor

section General
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D] (C : Type z) [DGCategory A C]
  (F : DGFunctor A D B) (P : BimoduleCategory A B C)

local notation "RP" => Functor.obj
  (BimoduleCategory.middleRightRestrictionFunctor A B D C F) P
local notation "LD" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B B D F)
  (BimoduleCategory.of A B B (Bimodule.diagonal A B))

-- 終端CのsmallnessやFの準同値性は不要。両作用を保持した通常のbimodule射の等式。
example :
    composeMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 RP) ≫
      (composeRightRestrictionIso A B D D C F LD RP).hom ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (middleRestrictionComparisonMap A B B D C F (Bimodule.diagonal A B)
          (BimoduleCategory.underlying A B C P)) ≫
      (BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
        (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom =
      (leftBimoduleUnitIso A D C (BimoduleCategory.underlying A D C RP)).hom :=
  leftUnitRestriction A B D C F P

variable [Small.{u} C]

-- 元のPのK-flat性を仮定しない。制限後に指定したRが右K-flatであればよい。
example (hC : localHomKFlat A C) (R : RightKFlatBimoduleCategory A D C)
    (q : R.obj ⟶ RP) (hq : BimoduleCategory.quasiIso A D C q) :
    (derivedBimoduleComposeResolutionComputation A D D C hC RP R q hq).hom.app
        ((bimoduleToDerived A D D).obj (rightKFlatDiagonal A D).obj) ≫
      (bimoduleToDerived A D C).map
        (composeMap A D D C (Bimodule.diagonalRestrictionMap A D B F) (𝟙 R.obj)) ≫
      (bimoduleToDerived A D C).map (composeRightRestrictionIso A B D D C F LD R.obj).hom ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (middleRestrictionResolvedMap A B B D C F
            (rightKFlatDiagonal A B).obj P R.obj q)) ≫
      (bimoduleToDerived A D C).map
        ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).map
          (leftBimoduleUnitIso A B C (BimoduleCategory.underlying A B C P)).hom) =
    (derivedBimoduleLeftUnitIso A D C hC).hom.app ((bimoduleToDerived A D C).obj RP) :=
  derivedLeftUnitRestriction_resolution A B D C F P hC R q hq
end General

-- 標数2でも対角比較と外側制限比較をcoend包含で計算できる。
theorem SerrePositivity.DifferentialGraded.Checks.leftUnitRestriction_charTwo
    (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
    (D : Type w) [DGCategory (ZMod 2) D] [Small.{0} D]
    (C : Type z) [DGCategory (ZMod 2) C] (F : DGFunctor (ZMod 2) D B)
    (P : BimoduleCategory (ZMod 2) B C) (d x : D) (c : C) :
    BalancedTensor.ι (ZMod 2) D
        ((BimoduleCategory.underlying (ZMod 2) D C
          ((BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) B D C F).obj P)).rightAt c)
        ((Bimodule.diagonal (ZMod 2) D).leftAt d) x ≫
      composeValueMap (ZMod 2) D D C (Bimodule.diagonalRestrictionMap (ZMod 2) D B F)
        (𝟙 ((BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) B D C F).obj P)) d c ≫
      (composeRightRestrictionValueIso (ZMod 2) B D D C F
        (Bimodule.leftRestriction (ZMod 2) B B D F (Bimodule.diagonal (ZMod 2) B))
        (Bimodule.rightRestriction (ZMod 2) B D C F
          (BimoduleCategory.underlying (ZMod 2) B C P)) d c).hom =
    (𝟙 ((BimoduleCategory.underlying (ZMod 2) B C P).value (F.obj x) c) ⊗ₘ F.map d x) ≫
      BalancedTensor.ι (ZMod 2) D
        ((BimoduleCategory.underlying (ZMod 2) D C
          ((BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) B D C F).obj P)).rightAt c)
        ((Bimodule.leftRestriction (ZMod 2) B B D F
          (Bimodule.diagonal (ZMod 2) B)).leftAt (F.obj d)) x :=
  ι_leftUnitRestriction_comparison (ZMod 2) B D C F P d x c

#print axioms ι_leftUnitRestriction_comparison
#print axioms leftUnitRestriction_value
#print axioms leftUnitRestriction
#print axioms leftUnitRestriction_augmentation_exchange
#print axioms leftUnitRestriction_augmentation
#print axioms leftUnitRestriction_localized_augmentation
#print axioms derivedLeftUnitRestriction_resolution
#print axioms derivedMiddleRestrictionComparison_calculation

#print axioms SerrePositivity.DifferentialGraded.Checks.leftUnitRestriction_charTwo
