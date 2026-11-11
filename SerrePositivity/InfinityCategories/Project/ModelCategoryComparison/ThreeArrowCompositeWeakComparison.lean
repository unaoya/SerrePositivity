module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.PaddedThreeWeakComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.PaddingColimitComparison

/-!
# 元の三列の標準射の後の padding 比較の弱同値性

概要：元の標準射と padding 比較の合成は弱ホモトピー同値となる。
方針：既存の比較ホモトピーを全 Kan 標的への Hom の π₀ 関手で検査する。
規約：任意の弱同値が anodyne 局所化で反転するとは仮定しない。
使われ方：padding の左逆と元の三列の標準射の弱同値性の回収。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma threeArrowPaddingComposite_isWeakHomotopyEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)) := by
  intro Z hZ
  have he := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.colimit_comparison_image_eq X Y
    (_root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents Z).rightOp
    (_root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents_inverts Z)
  have he' := congrArg Quiver.Hom.unop he
  change (_root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents Z).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedThreeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)).op =
    (_root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents Z).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)).op at he'
  change Function.Bijective ((_root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents Z).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weakEquivalences C) X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingColimitMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)).op)
  rw [← he']
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.paddedThreeComparison_isWeakHomotopyEquivalence X Y cof Z

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
