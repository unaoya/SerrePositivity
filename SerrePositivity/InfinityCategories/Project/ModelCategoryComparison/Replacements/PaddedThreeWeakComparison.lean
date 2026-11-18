module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.PaddedForwardDiagramComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakProperColimit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PaddedComparisonRecovery

/-!
# 元の padded な全語の余極限への三列の弱同値比較

概要：元の paddedThreeComparison 自身が弱ホモトピー同値となる。
方針：元の自然変換の全成分の弱同値性を proper 余極限へ移し、既存の因子分解を使う。
規約：元の全語の filtered 性を仮定しない。元の三列の標準射への接続は後続。
使われ方：padding 比較ホモトピーによる元の三列の標準射の弱同値性。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits _root_.HomotopicalAlgebra
open _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddedForwardColimitMap_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (colim.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.paddedForwardDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y))) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.weakProperColimitMap _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphDiagram_proper (weakEquivalences C) X Y).paddedForward
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphDiagram_proper (weakEquivalences C) X Y).padding
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.paddedForwardDiagramMap_isWeakHomotopyEquivalence X Y cof)

include cof in
lemma paddedThreeComparison_isWeakHomotopyEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedThreeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedForwardColimitIso H).inv :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  have hc := hi.comp (paddedForwardColimitMap_isWeakHomotopyEquivalence X Y cof)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedForwardColimitIso H).inv ≫
    colimMap (Functor.whiskerRight _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardInclusionNat (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⋙ H))) at hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedThreeComparison_fac] at hc
  exact hc

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
