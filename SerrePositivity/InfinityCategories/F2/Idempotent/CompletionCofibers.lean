module

public import SerrePositivity.InfinityCategories.F2.Idempotent.BicartesianZeroIsoLifting
public import SerrePositivity.InfinityCategories.F2.Idempotent.StrictImageRecovery
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionArrowRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionExact

/-!
概要：安定な元の ∞ 圏の任意の冪等完備化で、全ての元の辺に双カルテジアン cofiber が存在。
方針：元の辺の coherent retract と、完全な双普遍四角形の像の閉性で存在を回収する。
規約：元の指定辺そのものを下辺として保持。標的の安定性を入力にしない。
使われ方：HA 1.1.3.7 の新しい辺の普遍四角形の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 安定な元の圏の任意の冪等完備化の全ての辺には、指定辺を保つ双普遍 cofiber が存在。 -/
lemma IsIdempotentCompletion.bicartesian_cofiber_exists {C D : SSet.{u}}
    [Quasicategory C] [IsStable C] [Quasicategory D] (f : C ⟶ D)
    (hf : IsIdempotentCompletion f) {x y : D _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj D) x y) :
    ∃ s : CofiberSquare a, IsPullbackSquare s.square := by
  have : HasZeroVertex D := IsIdempotentCompletion.hasZeroVertex f hf
  let A := SSet.yonedaEquiv.symm a.edge
  obtain ⟨b, ⟨r⟩⟩ := IsIdempotentCompletion.arrow_retract f hf A
  let s := chosenCofiberSquare (edgeOfSimplex (SSet.yonedaEquiv b))
  let G := s.square ≫ f
  have hG : IsBicartesianZeroVertex (functorVertex G) := by
    apply (isBicartesianZeroVertex_functorVertex G).mpr
    refine ⟨IsIdempotentCompletion.map_isZeroVertex f hf s.zero_corner, ?_, ?_⟩
    · exact IsIdempotentCompletion.preservesPullbackSquare f hf s.square
        (IsStable.pullback_of_pushout s.toZeroTriangle s.isPushout)
    · exact IsIdempotentCompletion.preservesPushoutSquare f hf s.square s.isPushout
  let v : (bicartesianZeroSquares D) _⦋0⦌ := ⟨functorVertex G, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, Functor.map_id_apply]
    exact hG⟩
  let q := bicartesianZeroBottomProjection D
  have hqv : q.app (Opposite.op ⦋0⦌) v = functorVertex (b ≫ f) := by
    change functorVertex (squareBottomEdge ≫ (s.square ≫ f)) = _
    rw [← Category.assoc, s.bottom_edge]
    change functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv b) ≫ f) = _
    rw [Equiv.symm_apply_apply]
  obtain ⟨w, ⟨e⟩⟩ := IsIdempotentComplete.retract_iso_in_image
    (bicartesianZeroSquares_isIdempotentComplete hf.1) q
    (bicartesianZeroBottomProjection_isFullyFaithful D) v (functorVertex A)
    (by rw [hqv]; exact r)
  obtain ⟨z, hz⟩ := exists_strict_vertex_preimage_of_targetLifting q
    (F1B.KanEquivalenceLifting.invertibleTargetLifting
      (bicartesianZeroBottomProjection_kanEquivalenceLifting D))
    w (functorVertex A) e
  let H := (functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) D).symm z.val
  have hH : functorVertex H = z.val := (functorVertexEquiv _ _).apply_symm_apply _
  have hcond := fullSubcomplexOnVertices_vertex z
  change IsBicartesianZeroVertex z.val at hcond
  rw [← hH, isBicartesianZeroVertex_functorVertex] at hcond
  have hproj : q.app (Opposite.op ⦋0⦌) z = functorVertex (squareBottomEdge ≫ H) := by
    change ((pre squareBottomEdge).app D).app (Opposite.op ⦋0⦌) z.val = _
    rw [← hH]
    rfl
  have hbottom : squareBottomEdge ≫ H = A := functorVertex_injective (hproj.symm.trans hz)
  let t : CofiberSquare a := {
    square := H
    zero_corner := hcond.1
    bottom_edge := hbottom
    isPushout := hcond.2.2 }
  exact ⟨t, hcond.2.1⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
