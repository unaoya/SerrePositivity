module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedFactorPasteValue
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedCutResidualLength

/-!
# 任意の三因子の貼り戻し後の同じ生成矢の回収

概要：実際の余極限の任意の指定 prefix・生成矢・残りを貼って切ると、同じ生成矢を回収する。
方針：元の貼り戻しと切断の文字列回収式の先頭と残りを比較する。
規約：元の始域・終域・元の射を持つ Total 矢を回収する。
使われ方：貼り戻しの後の元の三因子全体の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma pasteNonempty_generator (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty W X Y).app n s)).1.val = s.1.val := by
  have h := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut_value W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty W X Y).app n s)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint_value W X Y s.1 s.2.1 s.2.2)
  exact (List.cons.inj h).1

lemma pasteNonempty_generator_index (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n) :
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty W X Y).app n s)).1 = s.1 :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty_generator W X Y s)

lemma pasteNonempty_residual_value (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty W X Y).app n s)).1.val.right Y).app n
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty W X Y).app n s)).2.2 =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W s.1.val.right Y).app n s.2.2 := by
  have h := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut_value W ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pasteNonempty W X Y).app n s)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget.pastePoint_value W X Y s.1 s.2.1 s.2.2)
  exact (List.cons.inj h).2

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FactorTarget
