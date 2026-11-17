module

public import SerrePositivity.EInfinity.Hammock.WordBackwardDecomposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPaddedBackwardBounds
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardContextErasureComparison

/-!
# 両隣に backward 列を持つ任意の元の列の挿入比較

概要：局所分解の比較を元の語と指定列へ戻し、padding された内部列にも適用する。
方針：語の厳密な等式と指定列の cast を同時に移送する。
規約：元の eraseInclusion の graph 写像自身を結論とする。
使われ方：padding された語の一列挿入と有限個の挿入の比較。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory _root_.HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)

lemma erasureGraphMap_transport {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (h : a = b) (j : Fin a.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion a j)) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion b (Fin.cast (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.length h) j))) := by
  cases h
  rfl

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

include cof in
lemma backwardColumnGraphMap_isWeakHomotopyEquivalence {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {p : Fin w.length}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardBounds w p) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w p)) := by
  have hk := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextErasureComparison.graphMap_isWeakHomotopyEquivalence
    h.prefixWord h.suffixWord h.leftLength h.rightLength X Y cof
  have hj : Fin.cast (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.length h.whole_eq)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn h.prefixWord h.suffixWord h.leftLength h.rightLength) =
        p := h.middle_column_cast
  have ht := (erasureGraphMap_transport X Y h.whole_eq
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.middleColumn h.prefixWord h.suffixWord h.leftLength h.rightLength)).1 hk
  rw [hj] at ht
  exact ht

include cof in
lemma paddedErasedGraphMap_isWeakHomotopyEquivalence (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length)
    (hp : w.direction p = .backward) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedColumn w p))) :=
  backwardColumnGraphMap_isWeakHomotopyEquivalence X Y cof (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddedBackwardBounds w p hp)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
