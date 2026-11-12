module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.RightCofinalFunctor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
概要：Kan 複体との積の射影は左右の fibration。
方針：Kan 因子のホーンを充填し、指定した底の単体と組にする。
規約：底の quasicategory 性は不要。モデル構造は用いない。
使われ方：Kerodon Proposition 7.2.1.5（Tag 02N5）、cofinal な射の弱同値性の検査。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：Kan 複体との積の射影は任意のホーンを持ち上げる。
方針：第一因子のホーン充填と第二因子の指定単体を直積に持ち上げる。
規約：次数と欠ける面は任意。
使われ方：積の射影の左右の fibration 性。 -/
lemma cofinalProductProjection_hasLiftingProperty_horn (Z B : SSet.{u}) [KanComplex Z]
    (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (horn (n + 1) i).ι (snd Z B) := by
  constructor
  intro a b sq
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (a ≫ fst Z B)
  refine CommSq.HasLift.mk' { l := lift F b, fac_left := ?_, fac_right := lift_snd _ _ }
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst]
    exact hF.symm
  · rw [Category.assoc, lift_snd]
    exact sq.w.symm

/-- 概要：Kan 複体との積の射影は left fibration。
方針：全ホーンの持ち上げを左ホーンに制限する。
規約：底 B は任意。
使われ方：left cofinality による Kan 標的への写像空間の検査。 -/
instance cofinalProductProjection_leftFibration (Z B : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (snd Z B) where
  mem := by
    intro A D j hj
    cases hj with
    | @intro n i hi => exact cofinalProductProjection_hasLiftingProperty_horn Z B n i

/-- 概要：Kan 複体との積の射影は right fibration。
方針：全ホーンの持ち上げを右ホーンに制限する。
規約：底 B は任意。
使われ方：right cofinality による Kan 標的への写像空間の検査。 -/
instance cofinalProductProjection_rightFibration (Z B : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (snd Z B) where
  mem := by
    intro A D j hj
    cases hj with
    | @intro n i hi => exact cofinalProductProjection_hasLiftingProperty_horn Z B n i

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
