module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetEndpoints

/-! # 元の読み替えの切断頂点の厳密な内部性
概要：元の最右内部頂点は、元の部分集合の最小・最大頂点の厳密な内部にある。
方針：元の端点回収と元の昇順列の狭義単調性・右側境界を使う。
規約：元の最小・最大を使う。使われ方：実削除零面・分割一面の入力条件。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
variable {n : ℕ} (m : ℕ) (v : Fin (m + 1 + 1) ↪o Fin (n + 1))
  (T : Finset (Fin (n + 1)))

/-- 元の切断頂点は、元の部分集合の同じ最小頂点より厳密に右。 -/
lemma simplexHADecodeSubset_cut_min
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    (simplexHADecodeSubset (m + 1) v T).min'
      (simplexHADecodeSubset_nonempty (m + 1) v T) < v (Fin.last (m + 1)) := by
  rw [simplexHADecodeSubset_min (m + 1) v T hb]
  apply v.strictMono
  change 0 < m + 1
  omega

/-- 元の右側集合が非空なら、切断頂点は元の同じ最大頂点より厳密に左。 -/
lemma simplexHADecodeSubset_cut_max (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    v (Fin.last (m + 1)) < (simplexHADecodeSubset (m + 1) v T).max'
      (simplexHADecodeSubset_nonempty (m + 1) v T) := by
  rw [simplexHADecodeSubset_max (m + 1) v T hT hb]
  exact hb _ (Finset.max'_mem T hT)

end SerrePositivity.KST.SConstruction
