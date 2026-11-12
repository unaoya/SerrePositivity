module

public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：標準単体の境界を、同じホーンと欠けた一面の合併として表示する。
方針：余次元一の面の被覆と、欠けた面へのホーンの逆像を計算する。
規約：ホーン番号は任意で、内ホーン性はこの幾何には不要。
使われ方：境界全体の source・target Hom を同じ貼合せに沿って比較する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 同じホーンに欠けた面を加えると、実際の標準境界になる。 -/
lemma horn_sup_missingFace (n : ℕ) (i : Fin (n + 1)) :
    horn.{u} n i ⊔ stdSimplex.face {i}ᶜ = boundary n := by
  apply le_antisymm
  · apply sup_le
    · rw [horn_eq_iSup]
      exact iSup_le (fun j ↦ face_singleton_compl_le_boundary j.val)
    · exact face_singleton_compl_le_boundary i
  · rw [boundary_eq_iSup]
    apply iSup_le
    intro j
    by_cases h : j = i
    · subst j
      exact le_sup_right
    · exact (face_le_horn j i h).trans le_sup_left

/-- 欠けた面にホーンを引き戻すと、その面自身の実際の境界となる。 -/
lemma horn_missingFace_preimage (n : ℕ) (i : Fin (n + 2)) :
    (horn.{u} (n + 1) i).preimage (stdSimplex.δ i) = boundary n := by
  ext ⟨⟨m⟩⟩ s
  simp only [Subcomplex.preimage_obj, Set.mem_preimage,
    mem_horn_iff_notMem_range, mem_boundary_iff_notMem_range]
  change (∃ j : Fin (n + 2), ∃ (_ : j ≠ i),
    j ∉ Set.range (fun k ↦ i.succAbove (s k))) ↔
      ∃ k : Fin (n + 1), k ∉ Set.range s
  constructor
  · rintro ⟨j, hj, h⟩
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    refine ⟨k, ?_⟩
    rintro ⟨l, hl⟩
    exact h ⟨l, congrArg i.succAbove hl⟩
  · rintro ⟨k, hk⟩
    refine ⟨i.succAbove k, i.succAbove_ne k, ?_⟩
    rintro ⟨l, hl⟩
    exact hk ⟨l, Fin.succAbove_right_injective hl⟩

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
