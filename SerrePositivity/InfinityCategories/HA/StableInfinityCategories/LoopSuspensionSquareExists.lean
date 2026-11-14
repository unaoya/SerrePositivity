module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopZeroOuterSpanColimit

/-!
概要：固定 span の余錐比較から suspension の普遍四角形と厳密切断を構成する。
方針：実 fiber の同型で始対象性を余極限性へ戻し、全境界持ち上げを使う。
規約：安定性・有限余極限は仮定しない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma suspensionSquare_nonempty_of_loopEquivalence {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) := by
  obtain ⟨b⟩ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSourceFiber_isContractibleKan X x).nonempty
  let d := b.val
  let p := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).symm d.val
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p = d.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).apply_symm_apply d.val
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_zeroOuterSpan_of_loopEquivalence s hs hΩ p (by
    rw [hp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex d)
  let F := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c
  have hP : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
    apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanVertex_square_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)).mp
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroOuterSpanVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F))
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_span, hp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex d
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 1 0) ∧ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 1) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsZeroCornerSquareVertex, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagram_functorVertex] using hP
  let w : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquares X) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hP⟩
  have hwd : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w = d := by
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan F) = d.val
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_span, hp]
  have hsource : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex F 0 0 = x := by
    calc
      _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSource X).app (Opposite.op ⦋0⦌) w :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex _ F).symm
      _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X).app (Opposite.op ⦋0⦌)
          ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w) := by
        exact (ConcreteCategory.congr_hom
          (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroCornerSquareSpan_source X) (Opposite.op ⦋0⦌)) w).symm
      _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroOuterSpanSource X).app (Opposite.op ⦋0⦌) d := by rw [hwd]
      _ = x := b.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero x)
  exact ⟨{
    square := F
    zero_corner := hz.2
    other_zero := hz.1
    source_eq := hsource
    isPushout := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout c hc }⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
