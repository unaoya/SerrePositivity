module
public import SerrePositivity.KST.SConstruction.SimplexHADeleteVertexOrder
public import SerrePositivity.KST.SConstruction.SimplexHAFaceVertexCount
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetCoordinate

/-! # 元の任意の内部面頂点を削除した読み替え集合
概要：元の列から面頂点を一つ除く操作は、同じ読み替え集合のその頂点の削除。
方針：元の succAbove の像と単射性、右側集合の厳密境界を使う。
規約：元の始点と右側集合を保持。使われ方：全零面での実生成射の削除公式。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の面座標の頂点だけを列から削除すると、同じ元の部分集合のその頂点を除く。 -/
lemma simplexHADeleteVertexOrder_subset {N : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 2) ↪o Fin (N + 1)) (T : Finset (Fin (N + 1)))
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    simplexHADecodeSubset m (simplexHADeleteVertexOrder m q v) T =
      (simplexHADecodeSubset (m + 1) v T).erase (v (simplexHAFaceVertex m q)) := by
  ext x
  rw [simplexHADecodeSubset_mem, Finset.mem_erase, simplexHADecodeSubset_mem]
  constructor
  · rintro (⟨j, rfl⟩ | ht)
    · constructor
      · exact fun h => (Fin.succAbove_ne (simplexHAFaceVertex m q) j) (v.injective h)
      · exact Or.inl ⟨(simplexHAFaceVertex m q).succAbove j, rfl⟩
    · exact ⟨ne_of_gt (simplexHAFaceVertex_tail_lt m v T q hb x ht), Or.inr ht⟩
  · rintro ⟨hne, (⟨j, rfl⟩ | ht)⟩
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg v h))
      exact Or.inl ⟨k, congrArg v hk⟩
    · exact Or.inr ht

/-- 元の右側一点の全零面では、削除座標は元の同じ面座標そのもの。 -/
lemma simplexHADeleteVertexOrder_coordinate {N : ℕ} (m : ℕ) (q : Fin (m + 1))
    (v : Fin (m + 2) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (m + 1)) < b)
    (hI : 2 ≤ (simplexHADecodeSubset (m + 1) v {b}).card) :
    (simplexSubsetEraseNormalizedCoordinate (simplexHADecodeSubset (m + 1) v {b}) hI
      (v (simplexHAFaceVertex m q)) (simplexHAFaceVertex_mem m v {b} q)
      (by
        rw [simplexHADecodeSubset_min (m + 1) v {b}
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)]
        exact simplexHAFaceVertex_first_lt m v q)
      (by
        rw [simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b)
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)]
        exact simplexHAFaceVertex_tail_lt m v {b} q
          (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) b (Finset.mem_singleton_self b))).val =
      q.val := by
  have h := simplexSubsetEraseNormalizedCoordinate_right_count _ hI _
    (simplexHAFaceVertex_mem m v {b} q)
    (show (simplexHADecodeSubset (m + 1) v {b}).min' _ < v (simplexHAFaceVertex m q) from by
      rw [simplexHADecodeSubset_min (m + 1) v {b}
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)]
      exact simplexHAFaceVertex_first_lt m v q)
    (show v (simplexHAFaceVertex m q) < (simplexHADecodeSubset (m + 1) v {b}).max' _ from by
      rw [simplexHADecodeSubset_max (m + 1) v {b} (Finset.singleton_nonempty b)
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb)]
      exact simplexHAFaceVertex_tail_lt m v {b} q
        (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) b (Finset.mem_singleton_self b))
  rw [simplexHAFaceVertex_right_count m v {b}
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hb) q, Finset.card_singleton] at h
  omega

end SerrePositivity.KST.SConstruction
