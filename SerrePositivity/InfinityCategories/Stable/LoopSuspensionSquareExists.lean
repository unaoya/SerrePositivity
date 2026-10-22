module
public import SerrePositivity.InfinityCategories.Stable.LoopZeroOuterSpanColimit

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
namespace SerrePositivity.InfinityCategories

/-- 同じ固定 span の普遍性と suspension の全単体構成。 -/
lemma suspensionSquare_nonempty_of_loopEquivalence {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0)) (x : X _⦋0⦌) :
    Nonempty (SuspensionSquare x) := by
  obtain ⟨b⟩ := (zeroOuterSpanSourceFiber_isContractibleKan X x).nonempty
  let d := b.val
  let p := (functorVertexEquiv _ X).symm d.val
  have hp : functorVertex p = d.val := (functorVertexEquiv _ X).apply_symm_apply d.val
  obtain ⟨c, hc⟩ := hasColimit_zeroOuterSpan_of_loopEquivalence s hs hΩ p (by
    rw [hp]
    exact fullSubcomplexOnVertices_vertex d)
  let F := coconeSquare c
  have hP : IsZeroCornerSquareVertex (functorVertex F) := by
    apply (zeroOuterSpanVertex_square_iff (functorVertex F)).mp
    change IsZeroOuterSpanVertex (functorVertex (pushoutSpan F))
    rw [coconeSquare_span, hp]
    exact fullSubcomplexOnVertices_vertex d
  have hz : IsZeroVertex (squareVertex F 1 0) ∧ IsZeroVertex (squareVertex F 0 1) := by
    simpa only [IsZeroCornerSquareVertex, squareDiagram_functorVertex] using hP
  let w : (zeroCornerSquares X) _⦋0⦌ := ⟨functorVertex F, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hP⟩
  have hwd : (zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w = d := by
    apply Subtype.ext
    change functorVertex (pushoutSpan F) = d.val
    rw [coconeSquare_span, hp]
  have hsource : squareVertex F 0 0 = x := by
    calc
      _ = (zeroCornerSquareSource X).app (Opposite.op ⦋0⦌) w :=
        (evaluateFunctorAt_functorVertex _ F).symm
      _ = (zeroOuterSpanSource X).app (Opposite.op ⦋0⦌)
          ((zeroCornerSquareSpan X).app (Opposite.op ⦋0⦌) w) := by
        exact (ConcreteCategory.congr_hom
          (NatTrans.congr_app (zeroCornerSquareSpan_source X) (Opposite.op ⦋0⦌)) w).symm
      _ = (zeroOuterSpanSource X).app (Opposite.op ⦋0⦌) d := by rw [hwd]
      _ = x := b.property.trans (pinchedConstant_zero x)
  exact ⟨{
    square := F
    zero_corner := hz.2
    other_zero := hz.1
    source_eq := hsource
    isPushout := coconeSquare_isPushout c hc }⟩
end SerrePositivity.InfinityCategories
