module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberPushoutComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceCofiberRotation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceExcision
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SquareTranspose

/-!
概要：有限極限と実 loop 同値から、全ての辺の実 cofiber を構成する。
方針：元の辺の fiber を切除で cofiber にし、その列を一回回転する。
規約：有限余極限や安定性を追加仮定にしない。
使われ方：一般安定性判定の全 cofiber の存在条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：指定した元の辺を底辺として持つ cofiber 四角形が存在する。
方針：同じ辺を右辺に持つ fiber 四角形を切除し、零終点を付加して回転する。
規約：指定辺との一致はホモトピー圏でなく実辺の等式。
使われ方：IsStable の cofiber_exists フィールド。 -/
lemma cofiberSquare_nonempty_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    {x y : X _⦋0⦌} (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) := by
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_fiberSquare_of_cospan_limits
    (fun p ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit p) f
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_of_isPullback_of_loopEquivalence s hs hΩ t.square t.isPullback
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberRotationRectangle_of_loopEquivalence
    s hs hΩ t.toZeroTriangle ht
  refine ⟨{
    square := r.rotatedZeroTriangle.square
    zero_corner := r.rotatedZeroTriangle.zero_corner
    isPushout := r.rotated_isCofiber
    bottom_edge := ?_ }⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare r.diagram 0) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_transpose]
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare_sharedEdge, r.left_eq]
  exact t.right_edge

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
