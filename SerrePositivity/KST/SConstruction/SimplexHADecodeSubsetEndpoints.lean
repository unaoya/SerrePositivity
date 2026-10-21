module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubset

/-! # 元の読み替え部分集合の実端点
概要：元の部分集合の最小頂点は列の始点、最大頂点は右側集合の最大頂点。
方針：元の列の単調性と元の右側境界で、全ての頂点を同じ両端で挟む。
規約：元の最小・最大と濃度を使う。使われ方：指定端点の Serre 生成射への接続。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の読み替え部分集合は、元の列の始点を含むので非空。 -/
lemma simplexHADecodeSubset_nonempty {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) :
    (simplexHADecodeSubset m v T).Nonempty :=
  ⟨v 0, (simplexHADecodeSubset_mem m v T _).mpr (Or.inl ⟨0, rfl⟩)⟩

/-- 元の右側集合が非空なら、元の読み替え部分集合は二点以上を持つ。 -/
lemma simplexHADecodeSubset_two {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) : 2 ≤ (simplexHADecodeSubset m v T).card := by
  rw [simplexHADecodeSubset_card m v T hb]
  have hp := Finset.card_pos.mpr hT
  omega

/-- 元の読み替え部分集合の最小頂点は、元の同じ昇順列の始点。 -/
lemma simplexHADecodeSubset_min {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    (simplexHADecodeSubset m v T).min' (simplexHADecodeSubset_nonempty m v T) = v 0 := by
  apply (Finset.min'_eq_iff _ _ _).mpr
  constructor
  · exact (simplexHADecodeSubset_mem m v T _).mpr (Or.inl ⟨0, rfl⟩)
  · intro x hx
    rcases (simplexHADecodeSubset_mem m v T x).mp hx with ⟨j, rfl⟩ | ht
    · exact v.monotone (Fin.zero_le j)
    · exact (v.monotone (Fin.zero_le (Fin.last m))).trans (hb x ht).le

/-- 元の読み替え部分集合の最大頂点は、元の右側集合の同じ最大頂点。 -/
lemma simplexHADecodeSubset_max {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    (simplexHADecodeSubset m v T).max' (simplexHADecodeSubset_nonempty m v T) = T.max' hT := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact (simplexHADecodeSubset_mem m v T _).mpr (Or.inr (Finset.max'_mem T hT))
  · intro x hx
    rcases (simplexHADecodeSubset_mem m v T x).mp hx with ⟨j, rfl⟩ | ht
    · exact (v.monotone (Fin.le_last j)).trans (hb _ (Finset.max'_mem T hT)).le
    · exact Finset.le_max' T x ht

end SerrePositivity.KST.SConstruction
