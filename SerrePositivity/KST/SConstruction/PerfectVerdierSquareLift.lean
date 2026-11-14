module
public import SerrePositivity.KST.SConstruction.PerfectVerdierRawSquare

/-! # 同じ四つの完備対象を持つ実 Verdier 四角形の持ち上げ
概要：元の安定圏値四角形の四頂点を判定し、同じ全単体を Cat^perf に持ち上げる。
方針：四辺から四角を厳密に回収し、全部分複体の全頂点条件を適用する。
規約：新しい四角形の選択はしない。使われ方：任意の実 Verdier 提示の coherent 提示。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

open scoped Simplicial

/-- 元の実四角形の四角は、左・中央・右端と元の零安定圏の同じ頂点。 -/
lemma perfectVerdierRawSquare_vertices (d : PerfectVerdierSequence.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 0 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.verdier.left ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 1 0 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.verdier.middle ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 1 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex d.right ∧
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 0 1 = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u} := by
  have hQ := perfectVerdierRawSquare_edges d
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (perfectVerdierRawSquare d)
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.verdier.inclusion).src_eq] at h
    exact h.symm
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_target (perfectVerdierRawSquare d)
    rw [hQ.1, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.verdier.inclusion).tgt_eq] at h
    exact h.symm
  constructor
  · have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (perfectVerdierRawSquare d)
    rw [hQ.2.2.2, Equiv.apply_symm_apply, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).tgt_eq] at h
    exact h.symm
  · have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target (perfectVerdierRawSquare d)
    rw [hQ.2.2.1, Equiv.apply_symm_apply,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory d.verdier.left)).tgt_eq] at h
    exact h.symm

/-- 同じ実四角形の全ての角は、coherent な冪等完備性を持つ。 -/
lemma perfectVerdierRawSquare_corner_complete (d : PerfectVerdierSequence.{u}) (i j : Fin 2) :
    perfectStableVertexPredicate (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) i j) := by
  have h := perfectVerdierRawSquare_vertices d
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject _).obj
  fin_cases i <;> fin_cases j
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 0 0)).obj
    rw [h.1, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact d.left_complete
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 0 1)).obj
    rw [h.2.2.2, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact perfectZeroCategory_isIdempotentComplete
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 1 0)).obj
    rw [h.2.1, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact d.middle_complete
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (perfectVerdierRawSquare d) 1 1)).obj
    rw [h.2.2.1, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
    exact d.right_complete

/-- 四角形の元の任意の零単体は、同じ完備安定対象を表す。 -/
lemma perfectVerdierRawSquare_vertex_complete (d : PerfectVerdierSequence.{u})
    (x : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) _⦋0⦌) :
    perfectStableVertexPredicate ((perfectVerdierRawSquare d).app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨x, y⟩ := x
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective y
  exact perfectVerdierRawSquare_corner_complete d i j

/-- 同じ全単体を保持して、元の実四角形を Cat^perf に持ち上げる。 -/
def perfectVerdierSquare (d : PerfectVerdierSequence.{u}) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift perfectStableVertexPredicate (perfectVerdierRawSquare d)
    (perfectVerdierRawSquare_vertex_complete d)

/-- 持ち上げた同じ四角形の包含後は、元の全単体を厳密に回収する。 -/
lemma perfectVerdierSquare_inclusion (d : PerfectVerdierSequence.{u}) :
    perfectVerdierSquare d ≫ perfectStableInfinityInclusion = perfectVerdierRawSquare d :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

end SerrePositivity.KST.SConstruction
