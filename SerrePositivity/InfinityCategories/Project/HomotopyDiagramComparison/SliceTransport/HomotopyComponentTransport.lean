module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.HomotopyEdgeNaturality

/-!
# 元のホモトピー成分の辺に沿う可逆性

概要：両端の像が可逆な辺に沿って同じホモトピーの成分の可逆性を移す。
方針：元の実辺における全自然性の四角形を使う。
規約：ホモトピーも成分も選び直さない。
使われ方：次数零から元の augmentation に沿う実右 Kan 単位の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SSet
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

lemma homotopyComponent_target_isInvertible {K E : SSet.{u}} {f g : K ⟶ E}
    (H : SSet.Homotopy f g) {x y : K _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj K) x y)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map f)))
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map g))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated := by
  have hX : IsIso (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) := hx
  have hF : IsIso (Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map f))) := hf
  have hG : IsIso (Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map g))) := hg
  have hC : IsIso (Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map f)) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.homotopy_edge_naturality H e]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map f))) _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
