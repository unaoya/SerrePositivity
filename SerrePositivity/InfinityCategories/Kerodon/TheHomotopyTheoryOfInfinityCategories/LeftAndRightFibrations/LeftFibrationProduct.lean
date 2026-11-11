module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：二つの left fibration の直積は left fibration。
方針：左ホーンの持ち上げを二射影で解き、直積へまとめる。
規約：二つの底は異なってよい。
使われ方：filtered な底の対角を引き戻して積の全空間比較を得る。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：left fibration は二項直積で閉じる。
方針：持ち上げ問題を両成分へ送り、二つの持ち上げを組にする。
規約：底の充填性は不要。使われ方：cofinal な対角の底変換。 -/
instance leftFibration_tensorHom {E D B C : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (p ⊗ₘ q) where
  mem := by
    intro A K i hi
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) i hi
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q) i hi
    refine ⟨?_⟩
    intro a b sq
    have sq₀ : CommSq (a ≫ fst E D) i p (b ≫ fst B C) := ⟨by
      rw [Category.assoc, ← tensorHom_fst, ← Category.assoc, sq.w, Category.assoc]⟩
    have sq₁ : CommSq (a ≫ snd E D) i q (b ≫ snd B C) := ⟨by
      rw [Category.assoc, ← tensorHom_snd, ← Category.assoc, sq.w, Category.assoc]⟩
    refine ⟨⟨{ l := lift sq₀.lift sq₁.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, sq₀.fac_left]
      · rw [Category.assoc, lift_snd, sq₁.fac_left]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, tensorHom_fst, ← Category.assoc, lift_fst, sq₀.fac_right]
      · rw [Category.assoc, tensorHom_snd, ← Category.assoc, lift_snd, sq₁.fac_right]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
