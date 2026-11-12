module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone

/-!
概要：指定全余錐を、その頂点からの元の辺に沿って新しい頂点へ延長する。
方針：全 coslice の left fibration に対して元の辺を始点固定で持ち上げる。
規約：図式全体を固定し、辺の可逆性を要求しない。
使われ方：小さい全図式の表示段への因子化を compact な可算終段へ接続する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の全余錐の頂点からの辺に沿って、同じ全図式の余錐を新しい頂点へ延長する。
方針：coslice 射影の左ファイブレーション性で全辺を持ち上げる。
規約：結論は元の全図式の JoinCocone である。
使われ方：compact 表示段から compact fiber 始域への全試験余錐の移送。 -/
lemma exists_cocone_of_edge_from_vertex {K C : SSet.{u}} [Quasicategory C]
    {r : K ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) {y : C _⦋0⦌} (e : C.Edge c.vertex y) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r, d.vertex = y := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection r
  obtain ⟨F, _, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source p c e.toTruncated
  let d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r) _⦋0⦌ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r).δ 0 (SSet.yonedaEquiv F)
  have h₀ := congrArg SSet.yonedaEquiv hF
  rw [SSet.yonedaEquiv_comp] at h₀
  have h : p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge :=
    h₀.trans (SSet.yonedaEquiv.apply_symm_apply e.toTruncated.edge)
  refine ⟨d, ?_⟩
  change p.app (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder r).δ 0 (SSet.yonedaEquiv F)) = y
  rw [SSet.δ_naturality_apply, h]
  exact e.tgt_eq

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
