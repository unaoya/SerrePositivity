module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativeTriangleComposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.EdgeTransportPointLift
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses

/-!
概要：transport の像と同じ fiber 成分にある任意の点へ、底の指定辺を保って持ち上げる。
方針：fiber 内の修正辺を輸送辺につなぎ、底の退化三角形を内側ホーン充填で持ち上げる。
規約：底の辺はホモトピー類でなく元の一単体そのもの。使われ方：貼り合わせた右余錐の脚の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- transport の像と同じ fiber 成分にある点には、指定した底の辺を厳密に保つ輸送辺が存在。 -/
lemma exists_edge_over_of_transport_component {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B _⦋0⦌} (e : B.Edge a b)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p e f)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (hw : SSet.π₀.mk (f.app (Opposite.op ⦋0⦌) v) = SSet.π₀.mk w) :
    ∃ k : E.Edge v.val w.val, (k.map p).edge = e.edge := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration p b
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_edge_of_transport_point p e f hf v
  obtain ⟨h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.nonempty_vertexIso_of_piZero_eq hw
  obtain ⟨l, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ h.hom
  let lE := (SSet.Edge.ofTruncated l).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)
  have hL : (lE.map p).edge = (SSet.Edge.id (X := B) b).edge := by
    have hh := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ B ↦ t.app (Opposite.op ⦋1⦌) l.edge)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp p b)
    exact hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one b)
  have ha : p.app (Opposite.op ⦋0⦌) v.val = a :=
    v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero a)
  have hb : p.app (Opposite.op ⦋0⦌) w.val = b :=
    w.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b)
  let eb : B.Edge (p.app _ v.val) (p.app _ w.val) :=
    ⟨e.edge, e.src_eq.trans ha.symm, e.tgt_eq.trans hb.symm⟩
  let t := SSet.Edge.CompStruct.compId e
  let tb : SSet.Edge.CompStruct (k.map p) (lE.map p) eb :=
    ⟨t.simplex, t.d₂.trans hk.symm, t.d₀.trans hL.symm, t.d₁⟩
  obtain ⟨k', _, hk', _⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_compStruct_over_innerFibration p k lE eb tb
  exact ⟨k', hk'⟩

/-- 既存の選んだ transport と同じ fiber 成分なら、底の実際の辺の持ち上げを得る。 -/
lemma exists_edge_over_of_edgeTransport_component {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {a b : B _⦋0⦌} (e : B.Edge a b)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (hw : SSet.π₀.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p e).app (Opposite.op ⦋0⦌) v) = SSet.π₀.mk w) :
    ∃ k : E.Edge v.val w.val, (k.map p).edge = e.edge :=
  exists_edge_over_of_transport_component p e _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p e) v w hw

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
