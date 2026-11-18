module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AllMarkedNative
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPointAssociativity

/-!
# 元の指定 hammock の点の合成と包含の合成保存

概要：指定部分圏自身の元の合成と包含による回収を固定する。
方針：元の同じ合成と相対関手による保存を指定部分圏へ代入する。
規約：指定因子を ambient の点に置き換えない。
使われ方：全因子列の接合点の指定因子どうしの合成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (X Y Z : Paths C)
  {n m : SimplexCategoryᵒᵖ}

def nativeComposePoint (p : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).obj n) (q : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W Y Z).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Z).obj n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ ⟨Z⟩ p q

lemma nativeComposePoint_simplex (θ : n ⟶ m) (p : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W Y Z).obj n) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeComposePoint W X Y Z ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).map θ p) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W Y Z).map θ q) =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Z).map θ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeComposePoint W X Y Z p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_simplex (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩ ⟨Z⟩ θ p q

lemma inclusion_composePoint (p : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).obj n) (q : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W Y Z).obj n) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Z).app n (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeComposePoint W X Y Z p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W.paths X Y Z ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W X Y).app n p) ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.inclusion W Y Z).app n q) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.composePoint_map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.inclusion W.paths) p q

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked
