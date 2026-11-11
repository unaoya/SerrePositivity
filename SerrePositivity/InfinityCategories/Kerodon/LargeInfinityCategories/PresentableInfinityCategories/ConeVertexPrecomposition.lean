module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RightFibrationEdgeTarget
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit

/-!
概要：指定した錐の頂点へ入る辺に沿って、元の全図式の錐を前合成する。
方針：錐の圏の右ファイブレーションで同じ辺を終点から持ち上げる。
規約：辺の可逆性を仮定せず、極限性は結論に含めない。
使われ方：解錐の頂点を compact 生成対象上の解へ変更する。

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

/-- 概要：錐頂点へ入る辺の始点を頂点とする、同じ図式の錐が存在する。
方針：sliceOver の射影に対する元の辺の持ち上げの始端を取る。
規約：元の図式と指定始点を厳密に保持する。
使われ方：小さい全解図式の生成解を頂点とする錐。 -/
lemma exists_cone_vertex_of_edge {K X : SSet.{u}} [Quasicategory X]
    {D : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D) {y : X _⦋0⦌} (e : X.Edge y c.vertex) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D, d.vertex = y := by
  obtain ⟨s, _, hs⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.rightFibration_liftEdge_target (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D) c e.toTruncated
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver D).δ 1 (SSet.yonedaEquiv s)
  refine ⟨d, ?_⟩
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv s) = e.edge := by
    rw [← SSet.yonedaEquiv_comp, hs]
    exact Equiv.apply_symm_apply _ e.edge
  have hn := ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection D).naturality (SimplexCategory.δ (1 : Fin 2)).op)
    (SSet.yonedaEquiv s)
  exact hn.trans ((congrArg (fun z ↦ X.δ 1 z) he).trans e.src_eq)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
