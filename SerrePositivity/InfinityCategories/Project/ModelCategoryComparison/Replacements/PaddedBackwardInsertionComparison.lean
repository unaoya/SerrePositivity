module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.BackwardColumnErasureComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPaddedErasureIso

/-!
# 任意の語の backward 一列挿入を padding した元の比較

概要：元の paddingFunctor.map (eraseInclusion w p) の graph 写像が弱同値になる。
方針：元の列の像の比較同型で始域を照合し、局所分解の弱同値性と合成する。
規約：元の写像自身を結論とし、弱同値の anodyne 局所化での反転は仮定しない。
使われ方：有限個の backward 列の挿入による paddedForwardDiagramMap の全成分。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra _root_.SerrePositivity.InfinityCategories
open _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C] (X Y : C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
lemma paddedBackwardInsertion_isWeakHomotopyEquivalence (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (p : Fin w.length)
    (hp : w.direction p = .backward) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w p))) := by
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (weakEquivalences C) X Y
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (G.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.eraseIso w p).hom) :=
    _root_.SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (by infer_instance)
  have he := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.paddedErasedGraphMap_isWeakHomotopyEquivalence X Y cof w p hp
  have hc := hi.comp he
  rw [← G.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.eraseIso_hom_fac] at hc
  exact hc

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
