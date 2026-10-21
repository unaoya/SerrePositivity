module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetRecursion

/-! # 元の読み替え部分集合の左右フィルター
概要：切断頂点での左・右・厳密右フィルターを、元の昇順列と右側集合で回収する。
方針：元の列の最後の頂点の上下関係と、元の右側境界で所属を場合分けする。
規約：共有頂点は両側に含む。使われ方：標準一面の実部分集合分割との接続。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
variable {n : ℕ} (m : ℕ) (v : Fin (m + 1 + 1) ↪o Fin (n + 1))
  (T : Finset (Fin (n + 1)))

/-- 元の左フィルターは、切断頂点までの元の昇順列の像そのもの。 -/
lemma simplexHADecodeSubset_filter_left
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    (simplexHADecodeSubset (m + 1) v T).filter (· ≤ v (Fin.last (m + 1))) =
      Finset.univ.map v.toEmbedding := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hle⟩ := Finset.mem_filter.mp hx
    rcases (simplexHADecodeSubset_mem (m + 1) v T x).mp hx with ⟨j, rfl⟩ | ht
    · exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · exact False.elim ((not_lt_of_ge hle) (hb x ht))
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_filter.mpr
      ⟨(simplexHADecodeSubset_mem (m + 1) v T _).mpr (Or.inl ⟨j, rfl⟩),
        v.monotone (Fin.le_last j)⟩

/-- 元の右フィルターは、元の右側集合に同じ切断頂点を加えた部分集合。 -/
lemma simplexHADecodeSubset_filter_right
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    (simplexHADecodeSubset (m + 1) v T).filter (v (Fin.last (m + 1)) ≤ ·) =
      insert (v (Fin.last (m + 1))) T := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hle⟩ := Finset.mem_filter.mp hx
    rcases (simplexHADecodeSubset_mem (m + 1) v T x).mp hx with ⟨j, rfl⟩ | ht
    · exact Finset.mem_insert.mpr (Or.inl (le_antisymm (v.monotone (Fin.le_last j)) hle))
    · exact Finset.mem_insert_of_mem ht
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | ht
    · exact Finset.mem_filter.mpr ⟨simplexHADecodeSubset_cut_mem m v T, le_rfl⟩
    · exact Finset.mem_filter.mpr
        ⟨(simplexHADecodeSubset_mem (m + 1) v T x).mpr (Or.inr ht), (hb x ht).le⟩

/-- 元の厳密な右フィルターは、同じ元の未処理の右側集合そのもの。 -/
lemma simplexHADecodeSubset_filter_strict_right
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    (simplexHADecodeSubset (m + 1) v T).filter (v (Fin.last (m + 1)) < ·) = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hlt⟩ := Finset.mem_filter.mp hx
    rcases (simplexHADecodeSubset_mem (m + 1) v T x).mp hx with ⟨j, rfl⟩ | ht
    · exact False.elim ((not_lt_of_ge (v.monotone (Fin.le_last j))) hlt)
    · exact ht
  · intro ht
    exact Finset.mem_filter.mpr
      ⟨(simplexHADecodeSubset_mem (m + 1) v T x).mpr (Or.inr ht), hb x ht⟩

/-- 元の左フィルターは、元の左部分の読み替えの右端を切断頂点一点にした集合。 -/
lemma simplexHADecodeSubset_filter_left_decode
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    (simplexHADecodeSubset (m + 1) v T).filter (· ≤ v (Fin.last (m + 1))) =
      simplexHADecodeSubset m (Fin.castSuccOrderEmb.trans v) {v (Fin.last (m + 1))} := by
  rw [simplexHADecodeSubset_filter_left m v T hb, simplexHADecodeRange_succ]
  simp only [simplexHADecodeSubset, Finset.union_singleton]

end SerrePositivity.KST.SConstruction
