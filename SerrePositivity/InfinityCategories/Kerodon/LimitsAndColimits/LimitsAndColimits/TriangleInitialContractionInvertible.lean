module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleInitialContraction

/-!
概要：元の可逆三角形は初頂点への変形の各成分を可逆にする。
方針：変形の三つの成分を、元の恒等辺・最初の辺・長辺で検査する。
規約：指定された変形の辺そのものの可逆性。
使われ方：可逆三角形の評価の関手同型。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ可逆三角形は、初頂点への変形の各指定成分を反転する。 -/
lemma triangleInitialContraction_mapped_isInvertible {Y : SSet.{u}}
    (f : (Δ[2] : SSet.{u}) ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalenceTriangleVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (a : (Δ[2] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleInitialContraction a).toTruncated.map
      ((truncation 2).map f)) := by
  have hi : ∀ i : Fin 3, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (Y.δ i (SSet.yonedaEquiv f))) := by
    intro i
    have h := hf i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.triangleFunctorVertexSimplex_functorVertex] at h
    exact h
  obtain ⟨j, rfl⟩ := (stdSimplex.obj₀Equiv.symm).surjective a
  fin_cases j
  · have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleInitialContraction.{u}
        (stdSimplex.obj₀Equiv.symm (0 : Fin 3))).toTruncated :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleInitialContraction_vertex_zero).mpr (by
        change IsIso (SSet.Truncated.HomotopyCategory.homMk _)
        rw [SSet.Truncated.HomotopyCategory.homMk_id]
        infer_instance)
    exact h.map f
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (Y.δ (2 : Fin 3) (SSet.yonedaEquiv f))) ?_).mpr (hi 2)
    change f.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleInitialContraction
        (stdSimplex.obj₀Equiv.symm (1 : Fin 3))).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleInitialContraction_vertex_one, ← SSet.yonedaEquiv_comp,
      stdSimplex.yonedaEquiv_δ_comp]
    rfl
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (Y.δ (1 : Fin 3) (SSet.yonedaEquiv f))) ?_).mpr (hi 1)
    change f.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleInitialContraction
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3))).edge = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleInitialContraction_vertex_two, ← SSet.yonedaEquiv_comp,
      stdSimplex.yonedaEquiv_δ_comp]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
