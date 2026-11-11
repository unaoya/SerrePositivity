module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientUniversalComparison

/-! # 元の普遍差の比較正方形の Cat^perf への持ち上げ
概要：同じ包含・比較道・完備化後の商から作った全正方形を Cat^perf に保つ。
方針：元の四辺で四角を回収し、恒等 lax 圏の coherent 冪等完備性も証明する。
規約：可換な射の類から四角形を選び直さない。使われ方：LT の fiber 列の貼り合わせ。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial
namespace PerfectLaxQuotient
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)

/-- 元の比較正方形の四角は、元の左端・lax 圏・完備化先・恒等 lax 圏。 -/
lemma universalRawSquare_vertices :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.left ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 1 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (laxCategory p q) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 1 1 =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex (laxCategory (𝟙 d.sequence.right) (𝟙 d.sequence.right)) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 0 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.sequence.right := by
  have hQ := d.universalRawSquare_edges
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source d.universalRawSquare
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).src_eq] at h
    exact h.symm
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target d.universalRawSquare
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).tgt_eq] at h
    exact h.symm
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target d.universalRawSquare
    rw [hQ.2.2.2, Equiv.apply_symm_apply,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (LaxUniversalDifference.exactLift p q d.sequence.projection)).tgt_eq] at h
    exact h.symm
  · have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopEdge_source d.universalRawSquare
    rw [hQ.2.1, Equiv.apply_symm_apply,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (IdentityLax.exactDiagonal d.sequence.right)).src_eq] at h
    exact h.symm

/-- 同じ比較正方形の四角は、全 coherent 冪等図式について完備。 -/
lemma universalRawSquare_corner_complete (i j : Fin 2) :
    perfectStableVertexPredicate (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare i j) := by
  have h := d.universalRawSquare_vertices
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject _).obj
  fin_cases i <;> fin_cases j
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 0 0)).obj
    rw [h.1, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact d.left_complete
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 0 1)).obj
    rw [h.2.2.2, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact d.sequence.right_complete
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 1 0)).obj
    rw [h.2.1, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact d.middle_complete
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.universalRawSquare 1 1)).obj
    rw [h.2.2.1, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact perfectLaxCategory_isIdempotentComplete (𝟙 d.sequence.right) (𝟙 d.sequence.right)
      d.sequence.right_complete d.sequence.right_complete

/-- 元の正方形の任意の零単体は、同じ完備対象を表す。 -/
lemma universalRawSquare_vertex_complete
    (x : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    perfectStableVertexPredicate (d.universalRawSquare.app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨x, y⟩ := x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  exact d.universalRawSquare_corner_complete i j

/-- 元の指定比較道と全単体を保持する、Cat^perf の普遍差の比較正方形。 -/
def universalSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift perfectStableVertexPredicate d.universalRawSquare
    d.universalRawSquare_vertex_complete

/-- Cat^perf へ持ち上げた後も、元の全正方形を厳密に回収する。 -/
lemma universalSquare_inclusion :
    d.universalSquare ≫ perfectStableInfinityInclusion = d.universalRawSquare :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
