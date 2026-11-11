module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice

/-!
概要：余極限余錐の頂点を指定した可逆辺に沿って移す。
方針：coslice の左ファイブレーションで辺を持ち上げ、始対象性を同型で移す。
規約：元の図式は固定する。余錐の全ての高次の整合性は持ち上げから得る。
使われ方：通常の filtered Kan colimit を実際の ∞ 余極限の頂点にする。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：可逆な頂点比較に沿って、図式を保った余極限余錐が存在する。
方針：可逆辺を元の余錐から持ち上げ、coslice の始対象性を保つ。
規約：新しい頂点は指定した y に厳密に一致する。使われ方：具体的な余極限頂点。 -/
lemma exists_colimitCone_vertex_of_invertible {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) {y : X _⦋0⦌}
    (e : X.Edge c.vertex y) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = y := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p
  obtain ⟨F, hF₀, hFq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source q c e.toTruncated
  let s := SSet.yonedaEquiv F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).δ 0 s
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p).δ 1 s = c := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀, Equiv.apply_symm_apply]
  let a : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) c d := ⟨s, hs, rfl⟩
  have hm : (a.map ((truncation 2).map q)).edge = e.edge := by
    change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
    rw [← SSet.yonedaEquiv_comp, hFq]
    exact Equiv.apply_symm_apply _ e.edge
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge q a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hm).2 he)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk a) := ha
  refine ⟨d, hc.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk a)), ?_⟩
  have ht := congrArg (fun z ↦ X.δ 0 z) hm
  change X.δ 0 (q.app (Opposite.op ⦋1⦌) s) = X.δ 0 e.edge at ht
  have hn := ConcreteCategory.congr_hom
    (q.naturality (SimplexCategory.δ (0 : Fin 2)).op) s
  exact hn.trans (ht.trans e.tgt_eq)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
