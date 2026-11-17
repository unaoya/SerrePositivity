module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.LocalizationNerveSource

/-!
# 元の弱同値射の局所化 nerve の頂点同型

概要：元の指定弱同値は同じ局所化 nerve の元の対象頂点を同型にする。
方針：同じ反転辺の homMk と全頂点比較を使う。
規約：元の局所化写像と頂点同値を変更しない。
使われ方：具体的 CAlg_R の任意頂点の実代数表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationNerveVertexIsoOfWeak {X Y : C.category} (f : X ⟶ Y)
    (hf : C.weakEquivalences f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv C X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv C Y) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap_inverts C
    (show ComposableArrows.mk₁ f ∈ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges C from ⟨_, _, f, hf, rfl⟩)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C)).toTruncated := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve C)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C))) at h
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map
        ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C)))
      (f := ((nerve.edgeMk f).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C)).toTruncated) ?_).mp h
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap_vertexIso C X).symm ≪≫
    asIso (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap C)).toTruncated) ≪≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveSourceMap_vertexIso C Y

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
