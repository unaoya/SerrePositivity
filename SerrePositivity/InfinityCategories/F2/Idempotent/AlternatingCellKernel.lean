module

public import SerrePositivity.InfinityCategories.F2.Idempotent.OddPositionFixity
public import SerrePositivity.InfinityCategories.F2.Idempotent.AlternatingCellBoundary

/-!
概要：元の全奇数位置を通る交互セルの単体は、元の全セル像により一意に決まる。
方針：元の固定された奇数位置と単調性で偶数位置も挟み、元の単体全体を回収する。
規約：退化単体も含む全次数の元の単体を扱う。
使われ方：Ret の元のセル貼付けの商の核。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の標準単体の頂点像が厳密に増えるなら、元の位置の順序も保たれる。 -/
lemma simplex_position_le_of_image_lt {N n : ℕ} (a : (Δ[N] : SSet.{u}) _⦋n⦌)
    (p q : Fin (n + 1)) (h : a p < a q) : p ≤ q := by
  by_contra hn
  have hq : q ≤ p := le_of_lt (lt_of_not_ge hn)
  exact (not_lt_of_ge (stdSimplex.monotone_apply a hq)) h

/-- 元の全奇数位置を通る単体は、元の同じ交互セルの全像から厳密に回収できる。 -/
lemma alternatingCell_eq_of_odd_hits {m n : ℕ} (a b : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (h : (alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (alternatingCell m).app (Opposite.op ⦋n⦌) b)
    (hhit : ∀ i : Fin m, ∃ v : Fin (n + 1), (a v).val = 2 * i.val + 1) : a = b := by
  obtain ⟨v, hva, hvb⟩ := alternatingCell_odd_positions_fixed_exists a b h hhit
  apply SSet.stdSimplex.ext
  intro p
  by_cases hp : (a p).val % 2 = 1
  · exact alternatingCell_equal_odd_of_fixed_positions a b h v hva hvb p hp
  have hbp : (b p).val % 2 ≠ 1 := fun hb ↦ hp ((alternatingCell_equal_source_iff h p).mpr hb)
  apply Fin.ext
  have haBound := (a p).isLt
  have hbBound := (b p).isLt
  rcases lt_trichotomy (a p).val (b p).val with hab | hab | hba
  · let i : Fin m := ⟨(a p).val / 2, by omega⟩
    have hai : (a (v i)).val = (a p).val + 1 := by
      rw [hva i]
      change 2 * ((a p).val / 2) + 1 = (a p).val + 1
      omega
    have hbi : (b (v i)).val = (a p).val + 1 := (hvb i).trans ((hva i).symm.trans hai)
    have hlt : a p < a (v i) := by change (a p).val < (a (v i)).val; rw [hai]; omega
    have hb := stdSimplex.monotone_apply b (simplex_position_le_of_image_lt a p (v i) hlt)
    change (b p).val ≤ (b (v i)).val at hb
    rw [hbi] at hb
    omega
  · exact hab
  · let i : Fin m := ⟨(a p).val / 2 - 1, by omega⟩
    have hai : (a (v i)).val = (a p).val - 1 := by
      rw [hva i]
      change 2 * ((a p).val / 2 - 1) + 1 = (a p).val - 1
      omega
    have hbi : (b (v i)).val = (a p).val - 1 := (hvb i).trans ((hva i).symm.trans hai)
    have hlt : a (v i) < a p := by change (a (v i)).val < (a p).val; rw [hai]; omega
    have hb := stdSimplex.monotone_apply b (simplex_position_le_of_image_lt a (v i) p hlt)
    change (b (v i)).val ≤ (b p).val at hb
    rw [hbi] at hb
    omega

/-- 元のセル境界に属さない単体は、元の全奇数位置を通る。 -/
lemma alternatingCell_odd_hits_of_not_boundary {m n : ℕ}
    (a : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (ha : a ∉ (alternatingCellBoundary m).obj (Opposite.op ⦋n⦌)) :
    ∀ i : Fin m, ∃ v : Fin (n + 1), (a v).val = 2 * i.val + 1 := by
  classical
  have hfull : alternatingSourceVertices m ⊆ Finset.univ.image (fun v : Fin (n + 1) ↦ a v) := by
    by_contra hn
    exact ha ((mem_missingFaceComplex (alternatingSourceVertices m) a).mpr hn)
  intro i
  let j : Fin (2 * m + 1) := ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩
  have hj : j ∈ alternatingSourceVertices m := by simp [alternatingSourceVertices, j]
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (hfull hj)
  exact ⟨v, congrArg Fin.val hv⟩

/-- 元のセルの同じ全像を持つ二つの単体は、同じ単体か、双方が元の境界に属する。 -/
lemma alternatingCell_kernel {m n : ℕ} (a b : (Δ[2 * m] : SSet.{u}) _⦋n⦌)
    (h : (alternatingCell m).app (Opposite.op ⦋n⦌) a =
      (alternatingCell m).app (Opposite.op ⦋n⦌) b) :
    a = b ∨ a ∈ (alternatingCellBoundary m).obj (Opposite.op ⦋n⦌) ∧
      b ∈ (alternatingCellBoundary m).obj (Opposite.op ⦋n⦌) := by
  classical
  by_cases ha : a ∈ (alternatingCellBoundary m).obj (Opposite.op ⦋n⦌)
  · right
    refine ⟨ha, ?_⟩
    by_contra hb
    have he := alternatingCell_eq_of_odd_hits b a h.symm
      (alternatingCell_odd_hits_of_not_boundary b hb)
    exact hb (he.symm ▸ ha)
  · exact Or.inl (alternatingCell_eq_of_odd_hits a b h
      (alternatingCell_odd_hits_of_not_boundary a ha))

end SerrePositivity.InfinityCategories.F2.Idempotent
