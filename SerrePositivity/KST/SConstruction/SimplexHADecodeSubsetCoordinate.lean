module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetDimensions
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCutBounds
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitCard
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitNormalizedCube

/-! # 元の読み替えの切断頂点の局所番号と面座標
概要：元の切断局所番号と削除零面・分割一面の座標を、左列長と右側頂点数で回収。
方針：元の左右濃度と右端座標の回収を、同じ元の部分集合に適用する。
規約：元の昇順列挙・面座標を保持。使われ方：実標準両面と読み替えの再帰の比較。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction

/-- 元の削除零面の濃度座標に一を加えると、同じ元の厳密右フィルターの頂点数。 -/
lemma simplexSubsetEraseNormalizedCoordinate_right_count {n : ℕ}
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) (j : Fin (n + 1)) (hj : j ∈ I)
    (hmin : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j)
    (hmax : j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    (simplexSubsetEraseNormalizedCoordinate I hI j hj hmin hmax).val + 1 =
      (I.filter (j < ·)).card := by
  have hc := simplexSubsetCoordinate_right_count I hI
    (simplexSubsetEraseCoordinate I hI j hj hmin hmax)
  rw [simplexSubsetEraseCoordinate_recovery] at hc
  exact hc.symm

/-- 元の切断頂点の局所番号は、元の左列から共有頂点までの同じ番号。 -/
lemma simplexHADecodeSubset_cut_index {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t)
    (hI : 2 ≤ (simplexHADecodeSubset (m + 1) v T).card) :
    (simplexSubsetVertexIndex (simplexHADecodeSubset (m + 1) v T) hI
      (v (Fin.last (m + 1))) (simplexHADecodeSubset_cut_mem m v T)).val = m + 1 := by
  have hc := simplexSubsetSplitLeft_card _ hI _ (simplexHADecodeSubset_cut_mem m v T)
    (simplexHADecodeSubset_left_two m v T hb)
  rw [simplexHADecodeSubset_left_card m v T hb] at hc
  omega

/-- 元の削除零面の座標は、元の右側集合の自由次元そのもの。 -/
lemma simplexHADecodeSubset_erase_coordinate {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t)
    (hI : 2 ≤ (simplexHADecodeSubset (m + 1) v T).card) :
    (simplexSubsetEraseNormalizedCoordinate (simplexHADecodeSubset (m + 1) v T) hI
      (v (Fin.last (m + 1))) (simplexHADecodeSubset_cut_mem m v T)
      (simplexHADecodeSubset_cut_min m v T hb) (simplexHADecodeSubset_cut_max m v T hT hb)).val =
      T.card - 1 := by
  have hc := simplexSubsetEraseNormalizedCoordinate_right_count _ hI _
    (simplexHADecodeSubset_cut_mem m v T) (simplexHADecodeSubset_cut_min m v T hb)
    (simplexHADecodeSubset_cut_max m v T hT hb)
  rw [simplexHADecodeSubset_filter_strict_right m v T hb] at hc
  omega

/-- 元の分割一面も、削除零面と同じ元の右側自由次元の座標。 -/
lemma simplexHADecodeSubset_split_coordinate {n : ℕ} (m : ℕ)
    (v : Fin (m + 1 + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t)
    (hI : 2 ≤ (simplexHADecodeSubset (m + 1) v T).card) :
    (simplexSubsetSplitNormalizedCoordinate (simplexHADecodeSubset (m + 1) v T) hI
      (v (Fin.last (m + 1))) (simplexHADecodeSubset_cut_mem m v T)
      (simplexHADecodeSubset_cut_min m v T hb) (simplexHADecodeSubset_cut_max m v T hT hb)).val =
      T.card - 1 := by
  rw [simplexSubsetSplitNormalizedCoordinate_eq]
  exact simplexHADecodeSubset_erase_coordinate m v T hT hb hI

end SerrePositivity.KST.SConstruction
