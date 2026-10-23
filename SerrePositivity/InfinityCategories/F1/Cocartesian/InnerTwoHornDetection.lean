module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FactorizationTriangle
public import SerrePositivity.InfinityCategories.F1.Cocartesian.Composition
public import SerrePositivity.InfinityCategories.F1.InnerTwoHornEdges

/-!
概要：二次内ホーン上で cocartesian 辺を保つ元の関手は、欠ける長辺も保つ。
方針：同じ長辺を二本の cocartesian 辺へ分解し、その像の合成性を使う。
規約：元の関手・長辺と底上の厳密な可換性を保持する。
使われ方：二次内ホーンへの元の cocartesian Hom の制限の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 二次内ホーン上で元の cocartesian 辺を保てば、元の全ての cocartesian 辺を保つ。 -/
lemma preservesCocartesianEdges_of_innerTwoHorn
    {E F : SSet.{u}} (p : E ⟶ (Δ[2] : SSet.{u})) [CocartesianFibration p]
    (q : F ⟶ (Δ[2] : SSet.{u})) [InnerFibration q]
    (H : E ⟶ F) (hH : H ≫ q = p)
    (hpres : ∀ e : E _⦋1⦌, IsCocartesianEdge p e →
      p.app (Opposite.op ⦋1⦌) e ∈ (horn 2 1).obj (Opposite.op ⦋1⦌) →
        IsCocartesianEdge q (H.app (Opposite.op ⦋1⦌) e)) :
    PreservesCocartesianEdges p q H := by
  intro e he
  by_cases hb : p.app (Opposite.op ⦋1⦌) e ∈ (horn 2 1).obj (Opposite.op ⦋1⦌)
  · exact hpres e he hb
  have hlong := innerTwoHorn_missing_edge_eq_long _ hb
  have hp : SSet.yonedaEquiv.symm e ≫ p = stdSimplex.δ (1 : Fin 3) ≫ 𝟙 Δ[2] := by
    rw [SSet.yonedaEquiv_symm_comp, hlong, Equiv.symm_apply_apply, Category.comp_id]
  obtain ⟨t, htp, hte, hfirst, hsecond⟩ := exists_cocartesianFactorizationTriangle p e he (𝟙 Δ[2]) hp
  have hmem (j : Fin 3) (hj : j ≠ 1) :
      p.app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (stdSimplex.δ j ≫ t)) ∈
        (horn 2 1).obj (Opposite.op ⦋1⦌) := by
    rw [← SSet.yonedaEquiv_comp, Category.assoc, htp, Category.comp_id]
    exact (objEquiv_symm_δ_mem_horn_iff j 1).mpr hj
  have ha := hpres _ hfirst (hmem 2 (by decide))
  have hc := hpres _ hsecond (hmem 0 (by decide))
  have hlong' := isCocartesianEdge_triangle_longEdge (t ≫ H) q
    (by simpa only [← SSet.yonedaEquiv_comp, Category.assoc] using ha)
    (by simpa only [← SSet.yonedaEquiv_comp, Category.assoc] using hc)
  have hval : SSet.yonedaEquiv (stdSimplex.δ 1 ≫ (t ≫ H)) =
      H.app (Opposite.op ⦋1⦌) e := by
    rw [← Category.assoc, hte, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rwa [hval] at hlong'

end SerrePositivity.InfinityCategories
