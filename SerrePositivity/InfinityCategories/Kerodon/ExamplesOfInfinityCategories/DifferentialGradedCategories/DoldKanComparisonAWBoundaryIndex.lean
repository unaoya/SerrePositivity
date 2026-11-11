module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWPullback

/-!
# AW の削除境界と切断の添字と符号

概要：削除点の切断点に対する位置ごとに、切断集合と標準境界の符号を計算する。
方針：filter と erase を交換し、切断点より前の点の集合を非交和へ分ける。
規約：標準境界の符号は削除点より小さい点数による。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW の chain map 性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

variable {α : Type*} [LinearOrder α] {J : Finset α} {i j : α}

/-- 概要：接頭部分の削除点より前の点は元の集合の削除点より前の点と同じである。
方針：削除点が切断点以下なら余分な上界条件は自動的に満たされる。
規約：削除点と切断点が等しい場合も含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の接頭部分の微分の符号。 -/
lemma before_left (hji : j ≤ i) : (J.filter (· ≤ i)).filter (· < j) = J.filter (· < j) := by
  ext a
  simp only [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, (h.2.trans_le hji).le⟩, h.2⟩⟩

/-- 概要：接頭部分の点数は切断点より前の点数に一を足したものである。
方針：接頭部分を切断点より前の集合と切断点の非交和に分ける。
規約：切断点は集合に属するとする。
使われ方：Kerodon 2.5.8（Tag 00S0） の Leibniz 係数の次数の計算。 -/
lemma card_left (hi : i ∈ J) : (J.filter (· ≤ i)).card = (J.filter (· < i)).card + 1 := by
  classical
  have he : J.filter (· ≤ i) = insert i (J.filter (· < i)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · intro h
      exact (lt_or_eq_of_le h.2).elim (fun ha ↦ Or.inr ⟨h.1, ha⟩) Or.inl
    · rintro (rfl | h)
      · exact ⟨hi, le_rfl⟩
      · exact ⟨h.1, h.2.le⟩
  rw [he, Finset.card_insert_of_notMem (by simp)]

/-- 概要：削除点より前の点数は切断点より前と接尾部分の削除点より前の和である。
方針：切断点未満と以上で集合を非交和に分ける。
規約：切断点は削除点以下とする。
使われ方：Kerodon 2.5.8（Tag 00S0） の接尾部分の微分の符号の比較。 -/
lemma card_before_right (hij : i ≤ j) :
    (J.filter (· < j)).card = (J.filter (· < i)).card +
      ((J.filter (i ≤ ·)).filter (· < j)).card := by
  classical
  have hu : J.filter (· < i) ∪ (J.filter (i ≤ ·)).filter (· < j) = J.filter (· < j) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans_le hij⟩
      · exact ⟨h.1.1, h.2⟩
    · intro h
      by_cases ha : a < i
      · exact Or.inl ⟨h.1, ha⟩
      · exact Or.inr ⟨⟨h.1, le_of_not_gt ha⟩, h.2⟩
  have hd : Disjoint (J.filter (· < i)) ((J.filter (i ≤ ·)).filter (· < j)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact not_lt_of_ge (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2
      (Finset.mem_filter.mp ha).2
  rw [← hu, Finset.card_union_of_disjoint hd]

/-- 概要：接頭部分の cochain 次数の Leibniz 符号は切断点より前の点数の符号である。
方針：接頭部分の濃度を使って次数を負の点数とし、negOnePow の負号を消す。
規約：整数単元の係数を整数として評価する。
使われ方：HA 1.3.1.13 の AW の微分の第二項の係数。 -/
lemma leibniz_sign (hi : i ∈ J) :
    (((1 - ((J.filter (· ≤ i)).card : ℤ)).negOnePow : ℤ)) =
      (-1 : ℤ) ^ (J.filter (· < i)).card := by
  have he : 1 - ((J.filter (· ≤ i)).card : ℤ) = -((J.filter (· < i)).card : ℤ) := by
    rw [card_left hi]
    push_cast
    omega
  rw [he, Int.negOnePow_neg, Int.coe_negOnePow_natCast]

/-- 概要：Leibniz 符号と接尾部分の削除符号の積は元の削除符号である。
方針：二つの点数の和の式とべきの加法則を使う。
規約：削除点は切断点以上とする。
使われ方：Kerodon 2.5.8（Tag 00S0） の右側削除項と全体境界の対応。 -/
lemma sign_right (hi : i ∈ J) (hij : i ≤ j) :
    (((1 - ((J.filter (· ≤ i)).card : ℤ)).negOnePow : ℤ)) *
      (-1 : ℤ) ^ ((J.filter (i ≤ ·)).filter (· < j)).card =
        (-1 : ℤ) ^ (J.filter (· < j)).card := by
  rw [leibniz_sign hi, ← pow_add, ← card_before_right hij]

/-- 概要：切断点の左の点を削除しても接尾部分は変わらない。
方針：filter と erase を交換し、削除点が接尾部分に属さないことを使う。
規約：削除点と切断点は異なる。
使われ方：Kerodon 2.5.8（Tag 00S0） の左側削除項の成分の比較。 -/
lemma erase_right_of_lt (hji : j < i) : (J.erase j).filter (i ≤ ·) = J.filter (i ≤ ·) := by
  classical
  rw [Finset.filter_erase]
  apply Finset.erase_eq_of_notMem
  simp only [Finset.mem_filter, not_and]
  intro _
  exact not_le_of_gt hji

/-- 概要：切断点の右の点を削除しても接頭部分は変わらない。
方針：filter と erase を交換し、削除点が接頭部分に属さないことを使う。
規約：削除点と切断点は異なる。
使われ方：Kerodon 2.5.8（Tag 00S0） の右側削除項の成分の比較。 -/
lemma erase_left_of_lt (hij : i < j) : (J.erase j).filter (· ≤ i) = J.filter (· ≤ i) := by
  classical
  rw [Finset.filter_erase]
  apply Finset.erase_eq_of_notMem
  simp only [Finset.mem_filter, not_and]
  intro _
  exact not_le_of_gt hij

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
