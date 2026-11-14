module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardContextColumn

/-!
# 元の全体の中央列と抽出した中央の脚の性質

概要：元の全体の同じ中央列の性質を、抽出した局所図式の中央の脚へ戻す。
方針：元の恒等関手との厳密な回収と、連結の列の移送を使う。
規約：性質は任意の射の性質でよく、自明性を未知の入力にしない。
使われ方：元の全部分圏の条件から右置換の入力の自明性を回収する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextMiddleProperty
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n m : ℕ) (X Y : C)

lemma middleColumn_property (P : MorphismProperty C)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.wholeWord a b n m) X Y) :
    P (S.arrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn a b n m)) ↔ P ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).middle.app S) := by
  have h : P (((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.rebuiltFunctor a b n m X Y).obj S).arrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn a b n m)) ↔
      P ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).middle.app S) := by
    change P ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.prefixDiagram a b n m X Y).obj S)
        ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).zigzagObj S))
      ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.suffixDiagram a b n m X Y).obj S)).arrow (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn a b n m)) ↔ _
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property P, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_right_property P]
    exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams.coreFamily a b n m X Y).middleColumn_property P S
  rw [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuiltFunctor_eq] at h
  exact h

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextMiddleProperty
