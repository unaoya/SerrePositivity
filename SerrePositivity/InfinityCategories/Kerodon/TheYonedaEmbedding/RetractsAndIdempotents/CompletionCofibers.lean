module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.BicartesianZeroIsoLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrictImageRecovery
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionArrowRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionExact

/-!
概要：安定な元の ∞ 圏の任意の冪等完備化で、全ての元の辺に双カルテジアン cofiber が存在。
方針：元の辺の coherent retract と、完全な双普遍四角形の像の閉性で存在を回収する。
規約：元の指定辺そのものを下辺として保持。標的の安定性を入力にしない。
使われ方：HA 1.1.3.7 の新しい辺の普遍四角形の構成。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 安定な元の圏の任意の冪等完備化の全ての辺には、指定辺を保つ双普遍 cofiber が存在。 -/
lemma IsIdempotentCompletion.bicartesian_cofiber_exists {C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D] (f : C ⟶ D)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) {x y : D _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj D) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare a, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare s.square := by
  have : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex D := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.hasZeroVertex f hf
  let A := SSet.yonedaEquiv.symm a.edge
  obtain ⟨b, ⟨r⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.arrow_retract f hf A
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv b))
  let G := s.square ≫ f
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsBicartesianZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isBicartesianZeroVertex_functorVertex G).mpr
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.map_isZeroVertex f hf s.zero_corner, ?_, ?_⟩
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.preservesPullbackSquare f hf s.square
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout s.toZeroTriangle s.isPushout)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion.preservesPushoutSquare f hf s.square s.isPushout
  let v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.bicartesianZeroSquares D) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, Functor.map_id_apply]
    exact hG⟩
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.bicartesianZeroBottomProjection D
  have hqv : q.app (Opposite.op ⦋0⦌) v = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (b ≫ f) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ (s.square ≫ f)) = _
    rw [← Category.assoc, s.bottom_edge]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (SSet.yonedaEquiv b) ≫ f) = _
    rw [Equiv.symm_apply_apply]
  obtain ⟨w, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete.retract_iso_in_image
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.bicartesianZeroSquares_isIdempotentComplete hf.1) q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.bicartesianZeroBottomProjection_isFullyFaithful D) v (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A)
    (by rw [hqv]; exact r)
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_strict_vertex_preimage_of_targetLifting q
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.EquivalenceLifting.invertibleTargetLifting
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.bicartesianZeroBottomProjection_kanEquivalenceLifting D))
    w (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex A) e
  let H := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) D).symm z.val
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H = z.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  have hcond := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex z
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsBicartesianZeroVertex z.val at hcond
  rw [← hH, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isBicartesianZeroVertex_functorVertex] at hcond
  have hproj : q.app (Opposite.op ⦋0⦌) z = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ H) := by
    change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app D).app (Opposite.op ⦋0⦌) z.val = _
    rw [← hH]
    rfl
  have hbottom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ H = A := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective (hproj.symm.trans hz)
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare a := {
    square := H
    zero_corner := hcond.1
    bottom_edge := hbottom
    isPushout := hcond.2.2 }
  exact ⟨t, hcond.2.1⟩

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
