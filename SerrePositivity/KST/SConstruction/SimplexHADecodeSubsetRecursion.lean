module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubsetEndpoints

/-! # 元の読み替え部分集合の最右頂点による再帰
概要：最右頂点の追加・削除と右側集合への移動を、元の同じ部分集合の等号で回収する。
方針：元の有限昇順列の像を最後の頂点と左部分に分け、境界の非所属を使う。
規約：元の頂点番号を保持。使われ方：標準零面と辺保持の実鎖射の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
variable {n : ℕ} (m : ℕ) (v : Fin (m + 1 + 1) ↪o Fin (n + 1))
  (T : Finset (Fin (n + 1)))

/-- 元の昇順列の像は、元の左部分の像に同じ最右頂点を一つ加えた集合。 -/
lemma simplexHADecodeRange_succ :
    Finset.univ.map v.toEmbedding = insert (v (Fin.last (m + 1)))
      (Finset.univ.map (Fin.castSuccOrderEmb.trans v).toEmbedding) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_univ, true_and,
    RelEmbedding.coe_toEmbedding]
  change (∃ j, v j = x) ↔ x = v (Fin.last (m + 1)) ∨ ∃ j : Fin (m + 1), v j.castSucc = x
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact Or.inl rfl
    · exact Or.inr ⟨j, rfl⟩
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨Fin.last (m + 1), rfl⟩
    · exact ⟨j.castSucc, hj⟩

/-- 元の全体部分集合は、元の左部分と右側集合に同じ切断頂点を一つ加えた集合。 -/
lemma simplexHADecodeSubset_succ :
    simplexHADecodeSubset (m + 1) v T = insert (v (Fin.last (m + 1)))
      (simplexHADecodeSubset m (Fin.castSuccOrderEmb.trans v) T) := by
  simp only [simplexHADecodeSubset, simplexHADecodeRange_succ, Finset.insert_union]

/-- 元の切断頂点は、同じ頂点を除いた左部分と右側集合には属さない。 -/
lemma simplexHADecodeSubset_cut_not_mem
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    v (Fin.last (m + 1)) ∉ simplexHADecodeSubset m (Fin.castSuccOrderEmb.trans v) T := by
  intro h
  rcases (simplexHADecodeSubset_mem m (Fin.castSuccOrderEmb.trans v) T _).mp h with
    ⟨j, hj⟩ | ht
  · have he : j.castSucc = Fin.last (m + 1) := v.injective hj
    exact Fin.castSucc_ne_last j he
  · exact (hb _ ht).false

/-- 元の最右内部頂点を削除した部分集合は、元の左部分と同じ右側集合で回収する。 -/
lemma simplexHADecodeSubset_erase
    (hb : ∀ t ∈ T, v (Fin.last (m + 1)) < t) :
    (simplexHADecodeSubset (m + 1) v T).erase (v (Fin.last (m + 1))) =
      simplexHADecodeSubset m (Fin.castSuccOrderEmb.trans v) T := by
  rw [simplexHADecodeSubset_succ, Finset.erase_insert
    (simplexHADecodeSubset_cut_not_mem m v T hb)]

/-- 元の最右内部頂点を右側集合へ移すと、元の全体部分集合をそのまま回収する。 -/
lemma simplexHADecodeSubset_insert_tail :
    simplexHADecodeSubset m (Fin.castSuccOrderEmb.trans v) (insert (v (Fin.last (m + 1))) T) =
      simplexHADecodeSubset (m + 1) v T := by
  rw [simplexHADecodeSubset_succ]
  simp only [simplexHADecodeSubset, Finset.union_insert]

/-- 元の切断頂点は、元の全体部分集合に含まれる。 -/
lemma simplexHADecodeSubset_cut_mem :
    v (Fin.last (m + 1)) ∈ simplexHADecodeSubset (m + 1) v T :=
  (simplexHADecodeSubset_mem (m + 1) v T _).mpr (Or.inl ⟨Fin.last (m + 1), rfl⟩)

end SerrePositivity.KST.SConstruction
