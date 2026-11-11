module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
概要：quasicategory を第二因子に持つ直積の第一射影の inner fibration 性。
方針：第二因子の内角ホーンを埋め、第一因子の指定された単体と組にする。
規約：第一因子の quasicategory 性は不要。
使われ方：comma の始域射影の充填性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：quasicategory を第二因子に持つ直積の第一射影は inner fibration。
方針：第二因子の終対象への射のホーン持ち上げと直積の普遍性を使う。
規約：第一因子は任意の単体集合。
使われ方：単位の comma を始域の上の inner fibration として扱う。 -/
instance innerFibration_productFst (X Y : SSet.{u}) [Quasicategory Y] :
    InnerFibration (fst X Y) where
  mem := by
    intro A B i hi
    have : HasLiftingProperty i (terminal.from Y) :=
      InnerFibration.mem (q := terminal.from Y) i hi
    constructor
    intro a b sq
    have sqY : CommSq (a ≫ snd X Y) i (terminal.from Y) (terminal.from B) :=
      ⟨Subsingleton.elim _ _⟩
    refine CommSq.HasLift.mk' { l := lift b sqY.lift, fac_left := ?_, fac_right := lift_fst _ _ }
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst]
      exact sq.w.symm
    · rw [Category.assoc, lift_snd]
      exact sqY.fac_left

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
