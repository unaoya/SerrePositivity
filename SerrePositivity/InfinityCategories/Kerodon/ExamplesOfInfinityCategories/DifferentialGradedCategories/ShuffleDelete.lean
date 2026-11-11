module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleInsert
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# shuffle の水平・垂直ステップ削除と挿入の逆対応

概要：指定位置の一つのステップを削除し、挿入と互いに逆であることを示す。
方針：指定位置以外の有限順序集合と Fin n の標準同値を使う。
規約：KST Construction A.5 の標準 shuffle。水平削除では所属、垂直削除では非所属を要求する。
使われ方：境界項と各因子の通常境界の有限な添字の対応。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：一つの水平ステップを削除する。
方針：指定位置を除いた水平集合を Fin n に戻す。
規約：KST A.5、水平ステップ数 p+1 が p になる。
使われ方：水平境界項を小さい shuffle へ送る。 -/
def ShuffleIndex.removeHorizontal {p n : ℕ} (s : ShuffleIndex (p + 1) (n + 1))
    (a : Fin (n + 1)) (ha : a ∈ s.val) : ShuffleIndex p n :=
  ⟨(s.val.subtype (· ≠ a)).map (finSuccAboveEquiv a).symm.toEmbedding, by
    rw [Finset.card_map, Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem ha, s.property]
    omega⟩

/-- 概要：一つの垂直ステップを削除する。
方針：水平集合を、指定位置以外の有限順序集合から Fin n に戻す。
規約：KST A.5、水平ステップ数 p は保つ。
使われ方：垂直境界項を小さい shuffle へ送る。 -/
def ShuffleIndex.removeVertical {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (a : Fin (n + 1)) (ha : a ∉ s.val) : ShuffleIndex p n :=
  ⟨(s.val.subtype (· ≠ a)).map (finSuccAboveEquiv a).symm.toEmbedding, by
    rw [Finset.card_map, Finset.card_subtype, Finset.filter_ne', Finset.erase_eq_of_notMem ha,
      s.property]⟩

/-- 概要：水平削除後の各ステップの所属は、元の標準包含の像で判定できる。
方針：有限集合の像の所属を逆同値で戻す。
規約：KST A.5。使われ方：挿入と削除が逆であることの確認。 -/
@[simp] lemma ShuffleIndex.removeHorizontal_mem {p n : ℕ} (s : ShuffleIndex (p + 1) (n + 1))
    (a : Fin (n + 1)) (ha : a ∈ s.val) (j : Fin n) :
    j ∈ (s.removeHorizontal a ha).val ↔ a.succAbove j ∈ s.val := by
  change j ∈ (s.val.subtype (· ≠ a)).map (finSuccAboveEquiv a).symm.toEmbedding ↔ _
  rw [Finset.mem_map_equiv]
  simp only [Equiv.symm_symm, finSuccAboveEquiv_apply, Finset.mem_subtype]

/-- 概要：垂直削除後の各ステップの所属は、元の標準包含の像で判定できる。
方針：有限集合の像の所属を逆同値で戻す。
規約：KST A.5。使われ方：挿入と削除が逆であることの確認。 -/
@[simp] lemma ShuffleIndex.removeVertical_mem {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (a : Fin (n + 1)) (ha : a ∉ s.val) (j : Fin n) :
    j ∈ (s.removeVertical a ha).val ↔ a.succAbove j ∈ s.val := by
  change j ∈ (s.val.subtype (· ≠ a)).map (finSuccAboveEquiv a).symm.toEmbedding ↔ _
  rw [Finset.mem_map_equiv]
  simp only [Equiv.symm_symm, finSuccAboveEquiv_apply, Finset.mem_subtype]

/-- 概要：水平挿入したステップを削除すると元の shuffle に戻る。
方針：全てのステップの所属を比較する。
規約：KST A.5。使われ方：境界の添字の対応の左逆。 -/
@[simp] lemma ShuffleIndex.removeHorizontal_insertHorizontal {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) :
    (s.insertHorizontal a).removeHorizontal a (s.insertHorizontal_mem a) = s := by
  apply Subtype.ext
  ext j
  rw [ShuffleIndex.removeHorizontal_mem, ShuffleIndex.insertHorizontal_mem_image]

/-- 概要：垂直挿入したステップを削除すると元の shuffle に戻る。
方針：全てのステップの所属を比較する。
規約：KST A.5。使われ方：境界の添字の対応の左逆。 -/
@[simp] lemma ShuffleIndex.removeVertical_insertVertical {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin (n + 1)) :
    (s.insertVertical a).removeVertical a (s.insertVertical_not_mem a) = s := by
  apply Subtype.ext
  ext j
  rw [ShuffleIndex.removeVertical_mem, ShuffleIndex.insertVertical_mem_image]

/-- 概要：削除した水平ステップを同じ位置へ挿入すると元に戻る。
方針：指定位置と、それ以外の標準包含の像の二つの場合で所属を比較する。
規約：KST A.5。使われ方：境界の添字の対応の右逆。 -/
@[simp] lemma ShuffleIndex.insertHorizontal_removeHorizontal {p n : ℕ}
    (s : ShuffleIndex (p + 1) (n + 1)) (a : Fin (n + 1)) (ha : a ∈ s.val) :
    (s.removeHorizontal a ha).insertHorizontal a = s := by
  apply Subtype.ext
  ext x
  by_cases hx : x = a
  · subst x
    simp only [ShuffleIndex.insertHorizontal_mem, ha]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hx
    rw [ShuffleIndex.insertHorizontal_mem_image, ShuffleIndex.removeHorizontal_mem]

/-- 概要：削除した垂直ステップを同じ位置へ挿入すると元に戻る。
方針：指定位置と、それ以外の標準包含の像の二つの場合で所属を比較する。
規約：KST A.5。使われ方：境界の添字の対応の右逆。 -/
@[simp] lemma ShuffleIndex.insertVertical_removeVertical {p n : ℕ}
    (s : ShuffleIndex p (n + 1)) (a : Fin (n + 1)) (ha : a ∉ s.val) :
    (s.removeVertical a ha).insertVertical a = s := by
  apply Subtype.ext
  ext x
  by_cases hx : x = a
  · subst x
    simp only [ShuffleIndex.insertVertical_not_mem, ha]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hx
    rw [ShuffleIndex.insertVertical_mem_image, ShuffleIndex.removeVertical_mem]

/-- 概要：水平挿入のデータは指定された水平ステップを持つ大きな shuffle と同値。
方針：挿入と水平削除を互いの逆にする。
規約：KST A.5、位置もデータに含める。
使われ方：境界の有限な添字の分類の基礎となる実同値。 -/
def horizontalInsertionEquiv (p n : ℕ) :
    (ShuffleIndex p n × Fin (n + 1)) ≃
      {z : ShuffleIndex (p + 1) (n + 1) × Fin (n + 1) // z.2 ∈ z.1.val} where
  toFun z := ⟨(z.1.insertHorizontal z.2, z.2), z.1.insertHorizontal_mem z.2⟩
  invFun z := (z.val.1.removeHorizontal z.val.2 z.property, z.val.2)
  left_inv z := by
    apply Prod.ext
    · exact z.1.removeHorizontal_insertHorizontal z.2
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.val.1.insertHorizontal_removeHorizontal z.val.2 z.property
    · rfl

/-- 概要：垂直挿入のデータは指定された垂直ステップを持つ大きな shuffle と同値。
方針：挿入と垂直削除を互いの逆にする。
規約：KST A.5、指定ステップは水平集合に属さない。
使われ方：垂直境界の有限な添字の分類の基礎となる実同値。 -/
def verticalInsertionEquiv (p n : ℕ) :
    (ShuffleIndex p n × Fin (n + 1)) ≃
      {z : ShuffleIndex p (n + 1) × Fin (n + 1) // z.2 ∉ z.1.val} where
  toFun z := ⟨(z.1.insertVertical z.2, z.2), z.1.insertVertical_not_mem z.2⟩
  invFun z := (z.val.1.removeVertical z.val.2 z.property, z.val.2)
  left_inv z := by
    apply Prod.ext
    · exact z.1.removeVertical_insertVertical z.2
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.val.1.insertVertical_removeVertical z.val.2 z.property
    · rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

