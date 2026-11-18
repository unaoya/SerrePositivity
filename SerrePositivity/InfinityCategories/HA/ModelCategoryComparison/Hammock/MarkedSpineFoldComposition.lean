module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineFoldData

/-!
# 元の因子列の評価による明示的な合成の保存

概要：指定因子と非指定生成矢の像からの評価は元の全因子列の合成を保存する。
方針：接合点での指定因子の合成保存を左の因子列の帰納で反復する。
規約：元の全指定因子を評価してから目標の圏で合成する。
使われ方：元の自由積からの拡張関手。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {n : SimplexCategoryᵒᵖ}
  {D : Type uD} [Category.{vD} D] (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData W n D)
  {X Y Z : Paths C}

lemma fold_prepend (p : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).obj n) (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Z n Y) :
    F.fold (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.prepend p t) = F.marked p ≫ F.fold t := by
  cases t with
  | nil Y q => exact F.marked_comp p q
  | cons Y g q t =>
    dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.prepend, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData.fold]
    rw [F.marked_comp, Category.assoc]

lemma fold_append (s : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Y n X) (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Z n Y) :
    F.fold (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.append s t) = F.fold s ≫ F.fold t := by
  induction s with
  | nil X p => exact F.fold_prepend p t
  | cons X g p s ih =>
    dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.append, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData.fold]
    rw [ih]
    simp only [Category.assoc]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData
