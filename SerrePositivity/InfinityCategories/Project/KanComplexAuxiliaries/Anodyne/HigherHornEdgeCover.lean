module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：三次元以上の標準ホーンは標準単体の全ての辺を含む。
方針：辺の二頂点と除外番号の三点だけでは、四点以上の頂点集合を覆えない。
規約：退化辺も含む全ての一次単体を覆う。
使われ方：高次内ホーンの付加で、cocartesian 辺の保存条件を反映する。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-- 三次元以上の標準ホーンの包含は、全ての一次単体を覆う。 -/
lemma horn_ι_edge_surjective_of_three_le {n : ℕ} (hn : 3 ≤ n) (i : Fin (n + 1)) :
    Function.Surjective ((horn.{u} n i).ι.app (Opposite.op ⦋1⦌)) := by
  intro σ
  let g : Fin 3 → Fin (n + 1) := Fin.cases i (Fin.cases (σ 0) (fun _ ↦ σ 1))
  have hg : ¬ Function.Surjective g := by
    intro h
    have hc := Fintype.card_le_of_surjective g h
    simp only [Fintype.card_fin] at hc
    omega
  simp only [Function.Surjective, not_forall, not_exists] at hg
  obtain ⟨j, hj⟩ := hg
  refine ⟨⟨σ, ?_⟩, rfl⟩
  rw [mem_horn_iff_notMem_range]
  refine ⟨j, (fun h ↦ hj 0 h.symm), ?_⟩
  rintro ⟨k, hk⟩
  fin_cases k
  · exact hj 1 hk
  · exact hj 2 hk

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
