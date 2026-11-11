module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.PointwiseHomotopyPath

/-!
概要：全頂点を含む部分図式を固定するホモトピーの点ごとの可逆性。
方針：各頂点の時間辺を部分図式内で計算し、恒等辺と照合する。
規約：固定条件は円柱の射の等式。関手同型の別の代表を選ばない。
使われ方：B1 の正方形全体の三辺固定の変形を可逆 path にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：固定された部分図式内の頂点の時間辺は恒等辺に等しい。
方針：相対条件を頂点の退化辺と時間の辺で評価する。
規約：端点の表示が違っても raw な一次単体は一致する。
使われ方：相対ホモトピーの点ごとの可逆性。 -/
lemma relativeHomotopy_vertex_edge_eq_id {A B X : SSet.{u}}
    (i : A ⟶ B) (a : A ⟶ X) {f g : B ⟶ X} (H : SSet.Homotopy f g)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ a)
    (v : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) v)).edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) (a.app (Opposite.op ⦋0⦌) v)).edge := by
  have hi : i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (i.app (Opposite.op ⦋0⦌) v) 1 := by
    exact ConcreteCategory.congr_hom
      (i.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) v
  have ha : a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (a.app (Opposite.op ⦋0⦌) v) 1 := by
    exact ConcreteCategory.congr_hom
      (a.naturality (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0).op) v
  have hh := congrArg
    (fun k : A ⊗ (Δ[1] : SSet.{u}) ⟶ X ↦
      k.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)) hH
  change H.h.app (Opposite.op ⦋1⦌)
    (i.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) =
      a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) at hh
  rw [hi, ha] at hh
  change H.h.app (Opposite.op ⦋1⦌)
    ((SSet.Truncated.Edge.id (X := (truncation 2).obj B) (i.app (Opposite.op ⦋0⦌) v)).edge,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge) = _
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one] using hh

/-- 概要：全頂点を含む部分図式を固定したホモトピーは点ごとに可逆。
方針：各頂点を部分図式から持ち上げ、時間辺が恒等辺であることを使う。
規約：全次数での全射性は要求せず、頂点上の全射性だけを使う。
使われ方：三辺固定の正方形比較を可逆 path へ持ち上げる。 -/
lemma relativeHomotopy_pointwise_isInvertible {A B X : SSet.{u}}
    (i : A ⟶ B) (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) (a : A ⟶ X)
    {f g : B ⟶ X} (H : SSet.Homotopy f g)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ a) :
    ∀ v : B _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H v).toTruncated := by
  intro v
  obtain ⟨w, rfl⟩ := hi v
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (relativeHomotopy_vertex_edge_eq_id i a H hH w)).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
