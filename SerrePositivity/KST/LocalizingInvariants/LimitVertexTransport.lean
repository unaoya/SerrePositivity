module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection

/-!
概要：指定した可逆な頂点比較に沿う極限錐の輸送。
方針：slice 射影の一次の右ホーンを充填し、slice 内の比較辺も保持する。
規約：図式と比較の元の辺を変えない。使われ方：置換済み BF fiber を頂点に持つ錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ConeVertexTransport

/-- 右ファイブレーションは指定された終点へ辺を持ち上げる。 -/
lemma rightLift_target {X Y : SSet.{u}} (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q]
    (x : X _⦋0⦌) {y : Y _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      y (q.app (Opposite.op ⦋0⦌) x)) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶ X,
      stdSimplex.δ 0 ≫ F = SSet.yonedaEquiv.symm x ∧
      F ≫ q = SSet.yonedaEquiv.symm e.edge := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := q) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro (1 : Fin 2) (by decide))
  have sq : CommSq (SSet.const x) (horn 1 1).ι q (SSet.yonedaEquiv.symm e.edge) := by
    constructor
    apply horn.hom_ext'
    intro j hj
    fin_cases j
    · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact (SSet.yonedaEquiv_symm_zero _).symm.trans
        (congrArg SSet.yonedaEquiv.symm e.tgt_eq.symm)
    · exact (hj rfl).elim
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  rw [← horn.ι_ι_assoc 1 0 (by decide), sq.fac_left, SSet.comp_const,
    SSet.yonedaEquiv_symm_zero]

/-- 極限錐の頂点を替え、元の比較辺上の slice の辺を保持する。 -/
lemma exists_limitCone {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) {y : X _⦋0⦌}
    (e : X.Edge y c.vertex) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone d ∧ d.vertex = y ∧
      ∃ a : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) d c,
        (a.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p))).edge = e.edge := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p
  obtain ⟨F, hF₁, hFq⟩ := rightLift_target q c e.toTruncated
  let s := SSet.yonedaEquiv F
  let d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 1 s
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p).δ 0 s = c := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁, Equiv.apply_symm_apply]
  let a : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p)) d c := ⟨s, rfl, hs⟩
  have hm : (a.map ((truncation 2).map q)).edge = e.edge := by
    change q.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv F) = e.edge
    rw [← SSet.yonedaEquiv_comp, hFq]
    exact Equiv.apply_symm_apply _ e.edge
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge q a
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hm).2 he)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk a) := ha
  refine ⟨d, hc.of_vertexIso (asIso (SSet.Truncated.HomotopyCategory.homMk a)).symm, ?_, a, hm⟩
  have ht := congrArg (fun z ↦ X.δ 1 z) hm
  have hn := ConcreteCategory.congr_hom
    (q.naturality (SimplexCategory.δ (1 : Fin 2)).op) s
  exact hn.trans (ht.trans e.src_eq)

end SerrePositivity.KST.LocalizingInvariants.ConeVertexTransport
