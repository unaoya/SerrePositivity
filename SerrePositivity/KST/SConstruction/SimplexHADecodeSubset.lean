module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeBounds
public import Mathlib.Data.Finset.Card

/-! # 元の読み替えの昇順列と右側集合が定める部分集合
概要：元の昇順頂点列の像と未処理の右側頂点集合の和を、同じ標準単体内で取る。
方針：元の右側境界から両集合の非交叉を証明し、実濃度と cube 次元を計算する。
規約：元の全頂点番号を保持。使われ方：読み替えの実鎖射と標準面射の比較。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の昇順列の像と未処理の右側集合を合わせた、元の同じ頂点部分集合。 -/
def simplexHADecodeSubset {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  Finset.univ.map v.toEmbedding ∪ T

/-- 元の部分集合の頂点は、元の昇順列の像または元の右側集合の頂点。 -/
lemma simplexHADecodeSubset_mem {n : ℕ} (m : ℕ) (v : Fin (m + 1) ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) (x : Fin (n + 1)) :
    x ∈ simplexHADecodeSubset m v T ↔ (∃ j, v j = x) ∨ x ∈ T := by
  simp only [simplexHADecodeSubset, Finset.mem_union, Finset.mem_map,
    Finset.mem_univ, true_and, RelEmbedding.coe_toEmbedding]

/-- 元の昇順列の像と元の未処理の右側集合は交わらない。 -/
lemma simplexHADecodeSubset_disjoint {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    Disjoint (Finset.univ.map v.toEmbedding) T := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
  exact (not_lt_of_ge (v.monotone (Fin.le_last j))) (hb _ ht)

/-- 元の頂点部分集合の実濃度は、元の列の長さと元の右側集合の濃度の和。 -/
lemma simplexHADecodeSubset_card {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    (simplexHADecodeSubset m v T).card = m + 1 + T.card := by
  rw [simplexHADecodeSubset,
    Finset.card_union_of_disjoint (simplexHADecodeSubset_disjoint m v T hb)]
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- 元の部分集合の cube 次元は、読み替えで使う元の左次元と右側自由頂点数の和。 -/
lemma simplexHADecodeSubset_dimension {n : ℕ} (m : ℕ)
    (v : Fin (m + 1) ↪o Fin (n + 1)) (T : Finset (Fin (n + 1)))
    (hb : ∀ t ∈ T, v (Fin.last m) < t) :
    (simplexHADecodeSubset m v T).card - 2 = m + T.card - 1 := by
  rw [simplexHADecodeSubset_card m v T hb]
  omega

/-- 元の左列が一点だけなら、右側集合に同じ始頂点を加えた部分集合を回収する。 -/
lemma simplexHADecodeSubset_zero {n : ℕ} (v : Fin 1 ↪o Fin (n + 1))
    (T : Finset (Fin (n + 1))) : simplexHADecodeSubset 0 v T = insert (v 0) T := by
  ext x
  rw [simplexHADecodeSubset_mem, Finset.mem_insert]
  constructor
  · rintro (⟨j, hj⟩ | ht)
    · have he : j = 0 := Fin.ext (by have hj' := j.isLt; omega)
      subst j
      exact Or.inl hj.symm
    · exact Or.inr ht
  · rintro (rfl | ht)
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr ht

end SerrePositivity.KST.SConstruction
