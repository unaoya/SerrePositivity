module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetFilters

/-! # 元の読み替えの左右フィルターの濃度と自由次元
概要：元の切断の左右の濃度と cube 次元を、元の左列と右側頂点数で計算する。
方針：元の左右フィルターの集合等号と、最右頂点の非所属を使う。
規約：共有頂点を両側で数える。使われ方：実 tensor 分割の二つの次元の同定。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
variable {n : ℕ} (m : ℕ) (v : Fin (m + 1 + 1) ↪o Fin (n + 1))
  (T : Finset (Fin (n + 1)))

/-- 元の左フィルターの濃度は、元の左列に共有頂点を含めた長さ。 -/
lemma simplexHADecodeSubset_left_card
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    ((simplexHADecodeSubset (m + 1) v T).filter (· ≤ v (Fin.last (m + 1)))).card = m + 2 := by
  rw [simplexHADecodeSubset_filter_left m v T hb]
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- 元の右フィルターの濃度は、元の右側集合の濃度に共有頂点を一つ加えた値。 -/
lemma simplexHADecodeSubset_right_card
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    ((simplexHADecodeSubset (m + 1) v T).filter (v (Fin.last (m + 1)) ≤ ·)).card = T.card + 1 := by
  rw [simplexHADecodeSubset_filter_right m v T hb]
  exact Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T _ hb)

/-- 元の左フィルターの cube 次元は、元の左列の同じ次元。 -/
lemma simplexHADecodeSubset_left_dimension
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    ((simplexHADecodeSubset (m + 1) v T).filter (· ≤ v (Fin.last (m + 1)))).card - 2 = m := by
  rw [simplexHADecodeSubset_left_card m v T hb]
  omega

/-- 元の右フィルターの cube 次元は、右側集合の頂点数から一を引いた値。 -/
lemma simplexHADecodeSubset_right_dimension
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    ((simplexHADecodeSubset (m + 1) v T).filter (v (Fin.last (m + 1)) ≤ ·)).card - 2 =
      T.card - 1 := by
  rw [simplexHADecodeSubset_right_card m v T hb]
  omega

/-- 元の左フィルターは、元の正長 bead を作る二点以上の部分集合。 -/
lemma simplexHADecodeSubset_left_two
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    2 ≤ ((simplexHADecodeSubset (m + 1) v T).filter (· ≤ v (Fin.last (m + 1)))).card := by
  rw [simplexHADecodeSubset_left_card m v T hb]
  omega

/-- 元の右側集合が非空なら、右フィルターも二点以上の正長 bead の頂点集合。 -/
lemma simplexHADecodeSubset_right_two (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    2 ≤ ((simplexHADecodeSubset (m + 1) v T).filter (v (Fin.last (m + 1)) ≤ ·)).card := by
  rw [simplexHADecodeSubset_right_card m v T hb]
  have hp := Finset.card_pos.mpr hT
  omega

end SerrePositivity.KST.SConstruction
