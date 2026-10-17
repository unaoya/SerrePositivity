module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestriction
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionResolved
public import Mathlib.Data.ZMod.Basic

/-! # 二つの中間圏の制限と結合子・指定モデルの検査

## 概要
二つの中間圏の制限と結合子・指定モデルの検査。

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
universe v w z t s
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory BimoduleTensor
variable (B : Type v) [DGCategory (ZMod 2) B] [Small.{0} B]
  (C : Type w) [DGCategory (ZMod 2) C] [Small.{0} C]
  (D : Type z) [DGCategory (ZMod 2) D] [Small.{0} D]
  (E : Type t) [DGCategory (ZMod 2) E] [Small.{0} E]
  (T : Type s) [DGCategory (ZMod 2) T]
  (P : BimoduleCategory (ZMod 2) B C) (Q : BimoduleCategory (ZMod 2) C E)
  (R : BimoduleCategory (ZMod 2) E T)

local notation "P₀" => BimoduleCategory.underlying (ZMod 2) B C P
local notation "Q₀" => BimoduleCategory.underlying (ZMod 2) C E Q
local notation "R₀" => BimoduleCategory.underlying (ZMod 2) E T R

-- 局所flatness、準同値性、終端Tのsmallnessなし。次数−2・3・−1。
theorem associatorMiddleRestriction_charTwo_negativeDegrees
    (F : DGFunctor (ZMod 2) D C) (b : B) (d : D) (e : E) (t : T)
    (τ : ((R₀).value e t).X (-2)) (q : ((Q₀).value (F.obj d) e).X 3)
    (p : ((P₀).value b (F.obj d)).X (-1)) :
    (middleRestrictionValueComponent (ZMod 2) B C D T F P₀
        (BimoduleTensor.compose (ZMod 2) C E T Q₀ R₀) b t 0)
      ((composeMapComponent (ZMod 2) B D T
        (𝟙 (BimoduleCategory.of (ZMod 2) B D
          (Bimodule.leftRestriction (ZMod 2) B C D F P₀)))
        (composeRightRestrictionIso (ZMod 2) C D E T F Q R).hom b t 0)
        ((associatorValueComponent (ZMod 2) B D E T
          (Bimodule.leftRestriction (ZMod 2) B C D F P₀)
          (Bimodule.rightRestriction (ZMod 2) C D E F Q₀) R₀ b t 0)
          (associatorLeftElement (ZMod 2) B D E T
            (Bimodule.leftRestriction (ZMod 2) B C D F P₀)
            (Bimodule.rightRestriction (ZMod 2) C D E F Q₀) R₀ b d e t τ q p
            (show (3 : ℤ) + -1 = 2 by decide) (by decide)))) =
    associatorRightElement (ZMod 2) B C E T P₀ Q₀ R₀ b (F.obj d) e t τ q p
      (show (-2 : ℤ) + 3 = 1 by decide) (by decide) :=
  associatorMiddleRestriction_left_component_element (ZMod 2) B C D E T F P Q R b d e t τ q p
    (show (3 : ℤ) + -1 = 2 by decide) (show (-2 : ℤ) + 3 = 1 by decide) (by decide)

theorem associatorSecondMiddleRestriction_charTwo_negativeDegrees
    (F : DGFunctor (ZMod 2) D E) (b : B) (c : C) (d : D) (t : T)
    (τ : ((R₀).value (F.obj d) t).X (-2)) (q : ((Q₀).value c (F.obj d)).X 3)
    (p : ((P₀).value b c).X (-1)) :
    (associatorValueComponent (ZMod 2) B C E T P₀ Q₀ R₀ b t 0)
      ((middleRestrictionValueComponent (ZMod 2) B E D T F
        (BimoduleTensor.compose (ZMod 2) B C E P₀ Q₀) R₀ b t 0)
        ((composeMapComponent (ZMod 2) B D T
          (composeLeftRestrictionIso (ZMod 2) B C E D F P Q).hom
          (𝟙 (BimoduleCategory.of (ZMod 2) D T
            (Bimodule.rightRestriction (ZMod 2) E D T F R₀))) b t 0)
          (associatorLeftElement (ZMod 2) B C D T P₀
            (Bimodule.leftRestriction (ZMod 2) C E D F Q₀)
            (Bimodule.rightRestriction (ZMod 2) E D T F R₀) b c d t τ q p
            (show (3 : ℤ) + -1 = 2 by decide) (by decide)))) =
    associatorRightElement (ZMod 2) B C E T P₀ Q₀ R₀ b c (F.obj d) t τ q p
      (show (-2 : ℤ) + 3 = 1 by decide) (by decide) :=
  associatorSecondMiddleRestriction_left_component_element (ZMod 2) B C D E T F P Q R b c d t τ q p
    (show (3 : ℤ) + -1 = 2 by decide) (show (-2 : ℤ) + 3 = 1 by decide) (by decide)

-- 制限後モデルの準同型性の保存には、後因子の右相対K-flat性だけを使う。
theorem middleRestrictionComposeAugmentation_charTwo
    (F : DGFunctor (ZMod 2) D C) (S : BimoduleCategory (ZMod 2) D E)
    (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor (ZMod 2) C D E F).obj Q)
    (hR : Bimodule.rightRelativeKFlat (ZMod 2) E T R₀)
    (hq : BimoduleCategory.quasiIso (ZMod 2) D E q) :
    BimoduleCategory.quasiIso (ZMod 2) D T
      (middleRestrictionComposeAugmentation (ZMod 2) C D E T F Q S R q) :=
  middleRestrictionComposeAugmentation_quasiIso (ZMod 2) C D E T F Q S R q hR hq

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded.BimoduleTensor
#check associatorIso_middleRestriction
#check associatorIso_secondMiddleRestriction
#check associatorIso_middleRestriction_resolved

#print axioms middleRestrictionValueComponent
#print axioms middleRestrictionValueComponent_eq
#print axioms middleRestrictionValueHom
#print axioms middleRestrictionValueHom_apply
#print axioms middleRestrictionValueHom_eq
#print axioms middleRestrictionValueComponent_element
#print axioms associatorIso_middleRestriction
#print axioms associatorMiddleRestriction_left_component_element
#print axioms associatorMiddleRestriction_right_component_element
#print axioms composeValueMap_middleRestriction_leftElement
#print axioms composeValueMap_rightRestriction_rightElement
#print axioms middleRestriction_rightElement
#print axioms associatorMiddleRestriction_left_path_element
#print axioms associatorMiddleRestriction_right_path_element
#print axioms associatorValueHom_middleRestriction
#print axioms associatorValue_middleRestriction
#print axioms associatorIso_secondMiddleRestriction
#print axioms associatorSecondMiddleRestriction_left_component_element
#print axioms associatorSecondMiddleRestriction_right_component_element
#print axioms composeValueMap_leftRestriction_leftElement
#print axioms middleRestriction_leftElement
#print axioms composeValueMap_middleRestriction_rightElement
#print axioms associatorSecondMiddleRestriction_left_path_element
#print axioms associatorSecondMiddleRestriction_right_path_element
#print axioms associatorValueHom_secondMiddleRestriction
#print axioms associatorValue_secondMiddleRestriction
#print axioms middleRestrictionComposeAugmentation
#print axioms middleRestrictionComposeAugmentation_quasiIso
#print axioms associatorIso_middleRestriction_resolved

open SerrePositivity.DifferentialGraded.Checks
#print axioms associatorMiddleRestriction_charTwo_negativeDegrees
#print axioms associatorSecondMiddleRestriction_charTwo_negativeDegrees
#print axioms middleRestrictionComposeAugmentation_charTwo
