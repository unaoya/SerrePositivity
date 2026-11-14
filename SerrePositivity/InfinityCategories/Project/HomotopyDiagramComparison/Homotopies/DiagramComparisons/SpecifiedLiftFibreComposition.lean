module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.TransportFibreEdgeComposition

/-!
概要：指定した実際の持ち上げ辺に、同じ fiber 内の修正辺を合成する。
方針：元の二辺を指定したまま、底の右退化二単体上で内ホーンを充填する。
規約：輸送辺を存在命題から選び直さない。使われ方：標準 prism の右辺を保つ修正三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- fiber の辺を全空間へ含めた一単体は、元の fiber の一単体の値そのもの。 -/
lemma fibreEdgeInclusion_raw {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌} (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).Edge x y) :
    (l.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)).edge = l.edge.val := rfl

/-- 指定した持ち上げ辺と fiber の修正辺を、底の右退化を保って同じ三角形へ合成する。 -/
lemma exists_compStruct_of_lift_and_fibre_edge {E B : SSet.{u}} (p : E ⟶ B)
    [InnerFibration p] {a b : B _⦋0⦌} (e : B.Edge a b)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋0⦌) (z w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (k₀ : E.Edge v.val z.val) (hk₀ : (k₀.map p).edge = e.edge)
    (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b).Edge z w) :
    ∃ (k : E.Edge v.val w.val) (t : SSet.Edge.CompStruct k₀ (l.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) k),
      (k.map p).edge = e.edge ∧
        p.app (Opposite.op ⦋2⦌) t.simplex = (SSet.Edge.CompStruct.compId e).simplex := by
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
  exact ⟨k, t, hk, ht⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
