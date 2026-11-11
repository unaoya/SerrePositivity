module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssociativity

/-!
# 単調写像による AW の切断集合の像

概要：単射な集合では切断と像が可換であり、両切断で単射なら全体でも単射となる。
方針：単調性と切断点の像の比較を使う。
規約：単調写像は全体で単射であるとは仮定しない。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW の面・退化との可換性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {J : Finset α} {j : α}
    {f : α → β}

/-- 概要：単射な集合では接頭部分の像は像の接頭部分である。
方針：逆向きは単調性で像の順序を比較し、単射性で元の順序へ戻す。
規約：切断点は元の集合に属する。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の第一因子の自然性。 -/
lemma image_left (hf : Monotone f) (hi : Set.InjOn f (J : Set α)) (hj : j ∈ J) :
    (J.filter (· ≤ j)).image f = (J.image f).filter (· ≤ f j) := by
  classical
  ext b
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, haj⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hf haj⟩
  · rintro ⟨⟨a, ha, rfl⟩, hfa⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    by_contra h
    have hja : j ≤ a := (lt_of_not_ge h).le
    have he : a = j := hi ha hj (le_antisymm hfa (hf hja))
    exact h he.le

/-- 概要：単射な集合では接尾部分の像は像の接尾部分である。
方針：逆向きは単調性で像の順序を比較し、単射性で元の順序へ戻す。
規約：切断点は元の集合に属する。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の第二因子の自然性。 -/
lemma image_right (hf : Monotone f) (hi : Set.InjOn f (J : Set α)) (hj : j ∈ J) :
    (J.filter (j ≤ ·)).image f = (J.image f).filter (f j ≤ ·) := by
  classical
  ext b
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hja⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hf hja⟩
  · rintro ⟨⟨a, ha, rfl⟩, hfa⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    by_contra h
    have haj : a ≤ j := (lt_of_not_ge h).le
    have he : j = a := hi hj ha (le_antisymm hfa (hf haj))
    exact h he.le

/-- 概要：単調写像が左右の切断上でともに単射なら集合全体でも単射である。
方針：切断点を跨ぐ同じ像の二点は切断点とも同じ像を持ち、両側の単射性で一致する。
規約：端点での切断と等しい点も含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の退化で AW の全項が零となることの証明。 -/
lemma injOn_of_cuts (hf : Monotone f) (hj : j ∈ J)
    (hl : Set.InjOn f ((J.filter (· ≤ j) : Finset α) : Set α))
    (hr : Set.InjOn f ((J.filter (j ≤ ·) : Finset α) : Set α)) :
    Set.InjOn f (J : Set α) := by
  have hc {a b : α} (ha : a ∈ J) (hb : b ∈ J) (haj : a ≤ j) (hjb : j ≤ b)
      (hab : f a = f b) : a = b := by
    have hfj : f a = f j := le_antisymm (hf haj) (by rw [hab]; exact hf hjb)
    have haj' := hl (Finset.mem_filter.mpr ⟨ha, haj⟩)
      (Finset.mem_filter.mpr ⟨hj, le_rfl⟩) hfj
    have hjb' := hr (Finset.mem_filter.mpr ⟨hj, le_rfl⟩)
      (Finset.mem_filter.mpr ⟨hb, hjb⟩) (hfj.symm.trans hab)
    exact haj'.trans hjb'
  intro a ha b hb hab
  by_cases haj : a ≤ j
  · by_cases hbj : b ≤ j
    · exact hl (Finset.mem_filter.mpr ⟨ha, haj⟩) (Finset.mem_filter.mpr ⟨hb, hbj⟩) hab
    · exact hc ha hb haj (le_of_not_ge hbj) hab
  · by_cases hbj : b ≤ j
    · exact (hc hb ha hbj (le_of_not_ge haj) hab.symm).symm
    · exact hr (Finset.mem_filter.mpr ⟨ha, le_of_not_ge haj⟩)
        (Finset.mem_filter.mpr ⟨hb, le_of_not_ge hbj⟩) hab

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWMapIndex
