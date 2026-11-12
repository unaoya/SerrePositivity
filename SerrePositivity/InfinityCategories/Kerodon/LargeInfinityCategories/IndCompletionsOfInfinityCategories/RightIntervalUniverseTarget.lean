module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightIntervalUniverseShape
/-!
概要：右区間円柱の宇宙比較は、元の全終点面を厳密に保つ。
方針：各次数の直積と標準単体の同型を計算する。
規約：全パラメーターで元の全射を保持する。
使われ方：補間全族の終点評価の回収。

対応節は Kerodon 9.3（Tag 06FR）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：元の右区間円柱の全終点面は同じ全終点面に写る。
方針：各次数で計算する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma rightIntervalUniverseShape_one (A : SSet.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightIntervalUniverseShape A = SSet.ι₁ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl
/-- 概要：逆比較でも元の全終点面を厳密に回収する。
方針：同型を消去する。規約：元の射を保持。使われ方：終点評価の相対補間。 -/
lemma rightIntervalUniverseShape_inv_one (A : SSet.{u}) :
    SSet.ι₁ ≫ inv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightIntervalUniverseShape A) =
      (SSet.uliftFunctor.{u + 1, u}).map (SSet.ι₁ : A ⟶ A ⊗ Δ[1]) := by
  calc
    _ = ((SSet.uliftFunctor.{u + 1, u}).map SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightIntervalUniverseShape A) ≫
        inv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightIntervalUniverseShape A) := by rw [rightIntervalUniverseShape_one]
    _ = _ := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
