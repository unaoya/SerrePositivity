module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategories
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ExactFunctorSpanCospanPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteLimitPreservationGeneration
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LimitPreservationShapeIso
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.EmptyShapeLimitCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableFiniteLimitsColimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-!
概要：安定圏間の元の完全関手は、有限形状の指定した全極限錐を保つ。
方針：零対象と引き戻しの保存を、空形状・点 cospan による有限生成へ渡す。
規約：有限極限保存を完全関手の追加入力にしない。
使われ方：実分母の有限図式の共通精密化を商側で検査する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の完全関手は、任意の有限図式の同じ全極限錐を保存する。 -/
lemma exactMap_map_isLimit_finite {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {K : SSet.{u}} [K.Finite] {p : K ⟶ B.obj}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom c) := by
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits B.obj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable B.obj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_isLimit_finite_of_empty_pointCospan q.hom ?_ ?_ c hc
  · intro T p d hd
    let : IsEmpty (((⊥ : T.Subcomplex) : SSet.{u}) _⦋0⦌) :=
      ⟨fun v => v.property⟩
    have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex d.vertex :=
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isLimitCone_iff_terminal_of_emptyVertices d).mp hd
    let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex B.obj
    have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex d.vertex :=
      z.isZero.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso z.isTerminal ht)
    apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isLimitCone_iff_terminal_of_emptyVertices
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone q.hom d)).mpr
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone_vertex]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := q.hom) _ hz).2
  · intro p d hd
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.map_isLimit_of_shapeIso q.hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornReverseIso 2 0 ≪≫ (SSet.opFunctor.mapIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointConeSpanIso).symm)
      (fun _ a ha => _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.exactFunctor_preserves_cospan_limit q.hom a ha) d hd

end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.4.1" (partial := direction) "仮定：安定準圏の間の完全関手（HA の完全⇒左・右完全の向きに一致）。結論：任意の有限極限および押し出しを保存する。右完全性を有限余極限全体で述べ、三条件の全方向をまとめた型は未確認（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.exactMap_map_isLimit_finite
