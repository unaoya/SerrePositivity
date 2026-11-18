module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedValueAppend
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedNonemptyImage

/-!
# 元の hammock の合成と元の非指定文字列評価

概要：元の余極限の合成は非指定文字列の順序付き連結へ評価される。
方針：各次数の元の標準射の共同全射性と元の全列の連結則を使う。
規約：元の composePoint・colimitValue・生成射の標準射を保持する。
使われ方：任意の三因子の貼り戻しの非空性と因子回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y Z : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma colimitValue_composePoint (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths Y Z).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Z).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X Y Z p q) =
      List.append ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n p) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W Y Z).app n q) := by
  obtain ⟨a, σ, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y) n p
  obtain ⟨b, τ, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths Y Z) n q
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions W.paths X Y Z a b σ τ
  have hv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.colimitValue_inclusion W X Z (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b)
    (σ.prod' τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor)
  have hp := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.colimitValue_inclusion W X Y a σ
  have hq := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.colimitValue_inclusion W Y Z b τ
  exact (congrArg ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Z).app n) hc).trans
    (hv.trans ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value_append W (σ.obj 0) (τ.obj 0)).trans (congrArg₂ List.append hp.symm hq.symm)))

lemma colimitValue_arrowPoint {A B : Paths C} (p : A ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W A B).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths p n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W p :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.colimitValue_inclusion W A B (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W.paths p n)).trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.value_forward W p)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators
