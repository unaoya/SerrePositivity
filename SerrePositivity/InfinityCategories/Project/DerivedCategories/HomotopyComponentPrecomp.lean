module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
/-!
概要：指定ホモトピーの全成分を、前合成と全時刻固定に対して同じ実辺として計算する。
方針：同じ退化一次単体で全円柱を評価する。
規約：ホモトピー類への置換を含まない。使われ方：右 Kan 輸送の頂点と元の単位成分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
/-- 前合成した全ホモトピーの成分は、元の同じ像の頂点での実成分。 -/
lemma homotopyComponent_precomp_edge {L K X : SSet.{u}} {f g : K ⟶ X}
    (H : SSet.Homotopy f g) (i : L ⟶ K) (a : L _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i) a).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) a)).edge := by
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (Truncated.Edge.id (X := (truncation 2).obj L) a).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  have hi := ConcreteCategory.congr_hom (i.naturality (SimplexCategory.σ (0 : Fin 1)).op) a
  exact congrArg (fun t => H.h.app (Opposite.op ⦋1⦌) (t, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hi
/-- 全円柱の台が等しければ、同じ頂点での実成分辺も等しい。 -/
lemma homotopyComponent_edge_of_raw_eq {K X : SSet.{u}} {f g f' g' : K ⟶ X}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g') (h : H.h = H'.h) (a : K _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H' a).edge :=
  congrArg (fun t : K ⊗ (Δ[1] : SSet.{u}) ⟶ X => t.app (Opposite.op ⦋1⦌)
    ((Truncated.Edge.id (X := (truncation 2).obj K) a).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) h
/-- 全時刻で固定された図式のホモトピーの同じ実成分は可逆。 -/
lemma homotopyComponent_isInvertible_of_fixed {K X : SSet.{u}} {f g : K ⟶ X}
    (H : SSet.Homotopy f g) (v : K ⟶ X) (h : H.h = fst K (Δ[1] : SSet.{u}) ≫ v)
    (a : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).edge =
      ((Truncated.Edge.id (X := (truncation 2).obj K) a).map ((truncation 2).map v)).edge := by
    exact congrArg (fun t : K ⊗ (Δ[1] : SSet.{u}) ⟶ X => t.app (Opposite.op ⦋1⦌)
      ((Truncated.Edge.id (X := (truncation 2).obj K) a).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) h
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (Truncated.Edge.id (X := (truncation 2).obj K) a) := by
    change IsIso (Truncated.HomotopyCategory.homMk
      (Truncated.Edge.id (X := (truncation 2).obj K) a))
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hi.map v)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
