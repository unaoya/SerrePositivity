module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativeTriangleComposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.EdgeTransportPointLift

/-!
概要：指定した fiber 内の修正辺を、底の辺と二単体を保って輸送辺へ織り込む。
方針：右修正辺の像が恒等辺であることを計算し、底の退化合成三角形を持ち上げる。
規約：修正辺そのものを入力し、合成三角形も返す。使われ方：指定境界経路による右枝の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 入力した fiber の修正辺と輸送辺を、底の退化二単体を保つ合成三角形へまとめる。 -/
lemma exists_transport_compStruct_of_fibre_edge {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] {a b : B _⦋0⦌} (e : B.Edge a b)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p e f)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).Edge (f.app (Opposite.op ⦋0⦌) v) w) :
    ∃ (k₀ : E.Edge v.val (f.app (Opposite.op ⦋0⦌) v).val)
      (k : E.Edge v.val w.val)
      (t : SSet.Edge.CompStruct k₀ (l.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) k),
      (k₀.map p).edge = e.edge ∧ (k.map p).edge = e.edge ∧
        p.app (Opposite.op ⦋2⦌) t.simplex = (SSet.Edge.CompStruct.compId e).simplex := by
  obtain ⟨k₀, hk₀⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_edge_of_transport_point p e f hf v
  let lE := l.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)
  have hL : (lE.map p).edge = (SSet.Edge.id (X := B) b).edge := by
    have hh := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ B ↦ s.app (Opposite.op ⦋1⦌) l.edge)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp p b)
    exact hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one b)
  have ha : p.app (Opposite.op ⦋0⦌) v.val = a := v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)
  have hb : p.app (Opposite.op ⦋0⦌) w.val = b := w.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b)
  let eb : B.Edge (p.app _ v.val) (p.app _ w.val) :=
    ⟨e.edge, e.src_eq.trans ha.symm, e.tgt_eq.trans hb.symm⟩
  let sb := SSet.Edge.CompStruct.compId e
  let tb : SSet.Edge.CompStruct (k₀.map p) (lE.map p) eb :=
    ⟨sb.simplex, sb.d₂.trans hk₀.symm, sb.d₀.trans hL.symm, sb.d₁⟩
  obtain ⟨k, t, hk, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_compStruct_over_innerFibration p k₀ lE eb tb
  exact ⟨k₀, k, t, hk₀, hk, ht⟩

/-- 合成二単体を三面の等式で表示し、終点の表示変更による依存型の照合を避ける。 -/
lemma exists_transport_composition_faces_of_fibre_edge {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] {a b : B _⦋0⦌} (e : B.Edge a b)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p e f)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).Edge (f.app (Opposite.op ⦋0⦌) v) w) :
    ∃ (k₀ : E.Edge v.val (f.app (Opposite.op ⦋0⦌) v).val)
      (k : E.Edge v.val w.val) (s : E _⦋2⦌),
      p.app (Opposite.op ⦋1⦌) k₀.edge = e.edge ∧
      p.app (Opposite.op ⦋1⦌) k.edge = e.edge ∧
      E.δ 2 s = k₀.edge ∧ E.δ 0 s = l.edge.val ∧ E.δ 1 s = k.edge ∧
      p.app (Opposite.op ⦋2⦌) s = (SSet.Edge.CompStruct.compId e).simplex := by
  obtain ⟨k₀, k, t, h₀, h, ht⟩ := exists_transport_compStruct_of_fibre_edge p e f hf v w l
  exact ⟨k₀, k, t.simplex, h₀, h, t.d₂, t.d₀, t.d₁, ht⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
