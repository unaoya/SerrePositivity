module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowCutDiagram

/-!
# 元の一文字の列からの同じ Total 生成矢の回収

概要：非指定列の消去が一文字なら、選択した元の生成矢はその文字自身である。
方針：元の firstCut_erasure の先頭を取る。
規約：元の全対象・元の射を持つ Total 矢を回収する。
使われ方：貼り戻しの後の同じ生成矢の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}

lemma rowGenerator_of_singleton (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (g : Quiver.Total C)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i = [g]) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i hi = g := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstCut_erasure W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowFirstCut W τ i hi 0)
  exact (Option.some.inj (congrArg List.head? (hc.symm.trans he))).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
