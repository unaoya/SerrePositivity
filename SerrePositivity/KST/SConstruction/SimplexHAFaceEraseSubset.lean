module
public import SerrePositivity.KST.SConstruction.SimplexHAFaceVertex

/-! # 元の面頂点を削除した読み替え部分集合
概要：元の内部頂点を削除しても両端点を保ち、元の二点以上の集合を得る。
方針：元の所属・厳密内部性と HA の有限集合削除補題を使う。
規約：元の頂点集合・最小最大と濃度を保持。使われ方：実零面像の HA 成分。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.InfinityCategories
variable {n : ℕ} (m : ℕ) (v : Fin (m + 2) ↪o Fin (n + 1))
  (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
  (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) (i : Fin (m + 1))
include hT hb

/-- 元の面頂点の削除は、元の同じ両端を含む二点以上の集合を残す。 -/
lemma simplexHAFaceErase_two :
    2 ≤ ((simplexHADecodeSubset (m + 1) v T).erase (v (simplexHAFaceVertex m i))).card := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_two
    ((simplexHADecodeSubset_mem (m + 1) v T _).mpr (Or.inl ⟨0, rfl⟩))
    ((simplexHADecodeSubset_mem (m + 1) v T _).mpr (Or.inr (Finset.max'_mem T hT)))
    (simplexHAFaceVertex_first_lt m v i)
    (simplexHAFaceVertex_tail_lt m v T i hb _ (Finset.max'_mem T hT))

/-- 元の面頂点を削除しても、最小頂点は元の列の始点。 -/
lemma simplexHAFaceErase_min :
    v 0 = ((simplexHADecodeSubset (m + 1) v T).erase (v (simplexHAFaceVertex m i))).min'
      (Finset.card_pos.mp (by have h := simplexHAFaceErase_two m v T hT hb i; omega)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_min
    (show IsLeast (simplexHADecodeSubset (m + 1) v T : Set (Fin (n + 1))) (v 0) from by
      rw [← simplexHADecodeSubset_min (m + 1) v T hb]
      exact Finset.isLeast_min' _ _) (simplexHAFaceVertex_first_lt m v i)

/-- 元の面頂点を削除しても、最大頂点は元の右側集合の最大頂点。 -/
lemma simplexHAFaceErase_max :
    T.max' hT =
      ((simplexHADecodeSubset (m + 1) v T).erase (v (simplexHAFaceVertex m i))).max'
        (Finset.card_pos.mp (by have h := simplexHAFaceErase_two m v T hT hb i; omega)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.erase_max
    (show IsGreatest (simplexHADecodeSubset (m + 1) v T : Set (Fin (n + 1))) (T.max' hT) from by
      rw [← simplexHADecodeSubset_max (m + 1) v T hT hb]
      exact Finset.isGreatest_max' _ _)
    (simplexHAFaceVertex_tail_lt m v T i hb _ (Finset.max'_mem T hT))

omit hT in
/-- 元の一面頂点削除後の濃度は、元の自由次元と右側頂点数を回収する。 -/
lemma simplexHAFaceErase_card :
    ((simplexHADecodeSubset (m + 1) v T).erase (v (simplexHAFaceVertex m i))).card =
      m + 1 + T.card := by
  have h := Finset.card_erase_add_one (simplexHAFaceVertex_mem m v T i)
  have hc := simplexHADecodeSubset_card (m + 1) v T hb
  omega

end SerrePositivity.KST.SConstruction
