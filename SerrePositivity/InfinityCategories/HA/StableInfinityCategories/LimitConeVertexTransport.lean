module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RightFibrationEdgeTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma exists_limitCone_vertex_of_invertible {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) {y : X _⦋0⦌}
    (e : X.Edge y c.vertex) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d ∧ d.vertex = y := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p
  obtain ⟨F, hF₁, hFq⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.rightFibration_liftEdge_target q c e.toTruncated
  let s := SSet.yonedaEquiv F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 1 s
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 0 s = c := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let a : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) d c := ⟨s, rfl, hs⟩
  have hm : (a.map ((truncation 2).map q)).edge = e.edge := by
    change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
    rw [← SSet.yonedaEquiv_comp, hFq]
    exact Equiv.apply_symm_apply _ e.edge
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge q a
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hm).2 he)
  have : IsIso (Truncated.HomotopyCategory.homMk a) := ha
  refine ⟨d, hc.of_vertexIso (asIso (Truncated.HomotopyCategory.homMk a)).symm, ?_⟩
  have ht := congrArg (fun z ↦ X.δ 1 z) hm
  change X.δ 1 (q.app (Opposite.op ⦋1⦌) s) = X.δ 1 e.edge at ht
  have hn := ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ (1 : Fin 2)).op) s
  exact hn.trans (ht.trans e.src_eq)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
