module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：二次内ホーンで欠ける辺は、標準二単体の同じ長辺だけである。
方針：零頂点を含まなければ零面、最終頂点を含まなければ最終面に属することを使う。
規約：退化辺も含む全ての一次単体を扱う。
使われ方：二次内ホーンでの cocartesian 辺の保存条件の反映。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-- 二次内ホーンに含まれない辺は、標準の長辺そのもの。 -/
lemma innerTwoHorn_missing_edge_eq_long (e : (Δ[2] : SSet.{u}) _⦋1⦌)
    (he : e ∉ (horn 2 1).obj (Opposite.op ⦋1⦌)) :
    e = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3)) := by
  have h0 : e 0 = 0 := by
    by_contra h0
    apply he
    rw [mem_horn_iff_notMem_range]
    refine ⟨0, by decide, ?_⟩
    rintro ⟨i, hi⟩
    have hm : e 0 ≤ e i := (stdSimplex.objEquiv e).toOrderHom.monotone (Fin.zero_le _)
    rw [hi] at hm
    exact h0 (le_antisymm hm (Fin.zero_le _))
  have h1 : e 1 = 2 := by
    by_contra h1
    apply he
    rw [mem_horn_iff_notMem_range]
    refine ⟨2, by decide, ?_⟩
    rintro ⟨i, hi⟩
    have hm : e i ≤ e 1 := (stdSimplex.objEquiv e).toOrderHom.monotone (Fin.le_last _)
    rw [hi] at hm
    exact h1 (le_antisymm (Fin.le_last _) hm)
  apply stdSimplex.ext
  intro i
  fin_cases i
  · exact h0
  · exact h1

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
