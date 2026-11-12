module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.CosliceHomotopy

/-!
概要：cocartesian な辺の基底のホモトピー類による終点の比較。
方針：辺を終点固定の持ち上げの空間へ入れ、基底写像空間の同型を持ち上げる。
規約：同じ始点、基底の同じ終点を固定する。
使われ方：B4 の指定自然変換の h での不変性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：指定した基底の終点を持つ辺の基底への像。
方針：元の辺を写し、両端を指定した表示へ戻す。
規約：始点は a≫p、終点は b。
使われ方：基底の辺の h での等式の型。 -/
def transportBaseEdge {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (b : B _⦋0⦌) {y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (hb : p.app (Opposite.op ⦋0⦌) y = b) :
    SSet.Truncated.Edge (X := (truncation 2).obj B) (SSet.yonedaEquiv (a ≫ p)) b where
  edge := p.app (Opposite.op ⦋1⦌) e.edge
  src_eq := (e.map ((truncation 2).map p)).src_eq.trans (SSet.yonedaEquiv_comp a p).symm
  tgt_eq := (e.map ((truncation 2).map p)).tgt_eq.trans hb

/-- 概要：cocartesian な辺を終点固定の持ち上げの空間の頂点にする。
方針：辺の coslice 頂点に cocartesian 性と基底の終点の条件を添える。
規約：辺の始点は a、基底の終点は b。
使われ方：基底の辺のホモトピーに沿う比較。 -/
def transportBaseEdgeVertex {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (b : B _⦋0⦌) {y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (hb : p.app (Opposite.op ⦋0⦌) y = b) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiber a p b) _⦋0⦌ := by
  let σ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a e
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p).app (Opposite.op ⦋0⦌) σ
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianCosliceVertex a p σ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.hasCocartesianHornLifting_congr p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge a e)).2 he
  have hy : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) σ = y := by
    have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a σ).tgt_eq
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge] at hh
    exact hh.symm.trans e.tgt_eq
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s = b := by
    change p.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) σ) = b
    rw [hy, hb]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportChoiceToBaseFiber a p s b hs (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportChoice a p s σ rfl hc)

/-- 概要：辺から作った持ち上げを終点で評価すると元の終点。
方針：coslice に戻した辺の終点の等式を使う。
規約：fiber の条件の証明の表示は問わない。
使われ方：持ち上げ空間内の同型を元の頂点へ適用する。 -/
lemma transportBaseEdgeVertex_target_val {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) (b : B _⦋0⦌) {y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (hb : p.app (Opposite.op ⦋0⦌) y = b) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberTarget a p b).app (Opposite.op ⦋0⦌)
      (transportBaseEdgeVertex a p b e hb he)).val = y := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a e) = y
  have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a e)).tgt_eq
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge] at hh
  exact hh.symm.trans e.tgt_eq

/-- 概要：辺から作った持ち上げの基底の辺は元の辺の基底への像。
方針：coslice の後合成と辺への復帰の自然性を使う。
規約：等式は両端を指定した辺として述べる。
使われ方：基底の h での等式との照合。 -/
lemma transportBaseEdgeVertex_base_edge {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) (b : B _⦋0⦌) {y : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (hb : p.app (Opposite.op ⦋0⦌) y = b) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.cosliceFiberEdge (a ≫ p) b ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberMap a p b).app (Opposite.op ⦋0⦌)
      (transportBaseEdgeVertex a p b e hb he)) = transportBaseEdge a p b e hb := by
  apply SSet.Truncated.Edge.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge (a ≫ p)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a e))).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_postcomp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge]
  rfl

/-- 概要：基底の辺が同じホモトピー類なら、cocartesian な持ち上げの終点は同じ fiber で同型。
方針：終点固定の持ち上げの空間へ入れ、基底の h の等式を持ち上げて評価する。
規約：始点は a、基底の終点は b。元の二つの終点の一致は要求しない。
使われ方：指定自然変換を h で変更したときの比較錐の不変性。 -/
lemma exists_kanTransportEndVertexIso_of_homMk_eq {E B : SSet.{u}} [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p]
    (b : B _⦋0⦌) {y z : E _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) y)
    (f : SSet.Truncated.Edge (X := (truncation 2).obj E) (SSet.yonedaEquiv a) z)
    (hy : p.app (Opposite.op ⦋0⦌) y = b) (hz : p.app (Opposite.op ⦋0⦌) z = b)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p f)
    (h : SSet.Truncated.HomotopyCategory.homMk (transportBaseEdge a p b e hy) =
      SSet.Truncated.HomotopyCategory.homMk (transportBaseEdge a p b f hz)) :
    ∃ (v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌), v.val = y ∧ w.val = z ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso v w) := by
  let t := transportBaseEdgeVertex a p b e hy he
  let v := transportBaseEdgeVertex a p b f hz hf
  have hh : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.cosliceFiberEdge (a ≫ p) b ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberMap a p b).app _ t)) =
      SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.cosliceFiberEdge (a ≫ p) b ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberMap a p b).app _ v)) := by
    rw [transportBaseEdgeVertex_base_edge, transportBaseEdgeVertex_base_edge]
    exact h
  obtain ⟨i⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.transportBaseFiberTarget_nonempty_iso_of_homMk_eq a p b t v hh
  exact ⟨_, _, transportBaseEdgeVertex_target_val a p b e hy he,
    transportBaseEdgeVertex_target_val a p b f hz hf, ⟨i⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
