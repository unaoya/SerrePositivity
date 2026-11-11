module

public import SerrePositivity.EInfinity.SimplicialLocalization.LocalizationNerveSource

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def localizationNerveVertexIsoOfWeak {X Y : C.category} (f : X ⟶ Y)
    (hf : C.weakEquivalences f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (localizationNerveVertexEquiv C X) (localizationNerveVertexEquiv C Y) := by
  have h := localizationNerveSourceMap_inverts C
    (show ComposableArrows.mk₁ f ∈ weakNerveEdges C from ⟨_, _, f, hf, rfl⟩)
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map (localizationNerveSourceMap C)).toTruncated := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := localizationNerve C)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map
        ((truncation 2).map (localizationNerveSourceMap C))) at h
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ComposableArrows.mk₁ f)).map
        ((truncation 2).map (localizationNerveSourceMap C)))
      (f := ((nerve.edgeMk f).map (localizationNerveSourceMap C)).toTruncated) ?_).mp h
    rfl
  exact (localizationNerveSourceMap_vertexIso C X).symm ≪≫
    asIso (Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (localizationNerveSourceMap C)).toTruncated) ≪≫
        localizationNerveSourceMap_vertexIso C Y

end SerrePositivity.EInfinity.SimplicialLocalization
