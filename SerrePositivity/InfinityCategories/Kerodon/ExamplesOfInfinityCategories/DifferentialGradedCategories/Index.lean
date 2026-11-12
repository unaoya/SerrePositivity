module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-! # dg nerve の部分集合の端点と次数

概要：内部点の削除と切断が端点を保つことと、成分の次数の和を証明する。
方針：有限集合の最小元・最大元の一意性と濃度の加法性を使う。
規約：HA Construction 1.3.1.6 を cochain 次数 `2-|I|` で読む。
使われ方：単体の方程式を端点・次数の cast なしに記述する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

variable {α : Type*} [LinearOrder α] {I : Finset α} {a b j : α}

omit [LinearOrder α] in
/-- 概要：二点以上ある集合は空でない。方針：濃度の正値性を使う。
規約：HA 1.3.1.6 の端点を `min'` と `max'` で読む。使われ方：端点の引数。 -/
lemma nonempty (h : 2 ≤ I.card) : I.Nonempty := Finset.card_pos.mp (by omega)

/-- 概要：異なる二点を含む集合の濃度は二以上。方針：二点集合の包含で比較する。
規約：HA 1.3.1.6。使われ方：削除・切断後の成分の定義域を保証する。 -/
lemma two_le_card (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) : 2 ≤ I.card := by
  have h : ({a, b} : Finset α) ⊆ I := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  simpa [hab] using Finset.card_le_card h

/-- 概要：内部点を消しても少なくとも二点残る。方針：両端が残ることを使う。
規約：HA 1.3.1.6。使われ方：削除成分の濃度条件。 -/
lemma erase_two (ha : a ∈ I) (hb : b ∈ I) (haj : a < j) (hjb : j < b) :
    2 ≤ (I.erase j).card := by
  apply two_le_card (a := a) (b := b)
  · exact Finset.mem_erase.mpr ⟨ne_of_lt haj, ha⟩
  · exact Finset.mem_erase.mpr ⟨ne_of_gt hjb, hb⟩
  · exact ne_of_lt (haj.trans hjb)

/-- 概要：内部点の削除は最小元を保つ。方針：最小元の所属と下界性を継承する。
規約：HA 1.3.1.6。使われ方：削除成分の始点条件。 -/
lemma erase_min (ha : IsLeast (I : Set α) a) (haj : a < j)
    (h : (I.erase j).Nonempty) : a = (I.erase j).min' h := by
  symm
  apply (Finset.isLeast_min' _ h).unique
  exact ⟨Finset.mem_erase.mpr ⟨ne_of_lt haj, ha.1⟩,
    fun _ hk => ha.2 (Finset.mem_erase.mp hk).2⟩

/-- 概要：内部点の削除は最大元を保つ。方針：最大元の所属と上界性を継承する。
規約：HA 1.3.1.6。使われ方：削除成分の終点条件。 -/
lemma erase_max (hb : IsGreatest (I : Set α) b) (hjb : j < b)
    (h : (I.erase j).Nonempty) : b = (I.erase j).max' h := by
  symm
  apply (Finset.isGreatest_max' _ h).unique
  exact ⟨Finset.mem_erase.mpr ⟨ne_of_gt hjb, hb.1⟩,
    fun _ hk => hb.2 (Finset.mem_erase.mp hk).2⟩

/-- 概要：内部点で左に切ると二点以上残る。方針：始点と切断点を含む。
規約：HA 1.3.1.6。使われ方：左成分の濃度条件。 -/
lemma left_two (ha : a ∈ I) (hj : j ∈ I) (haj : a < j) :
    2 ≤ (I.filter (· ≤ j)).card :=
  two_le_card (Finset.mem_filter.mpr ⟨ha, haj.le⟩)
    (Finset.mem_filter.mpr ⟨hj, le_rfl⟩) (ne_of_lt haj)

/-- 概要：内部点で右に切ると二点以上残る。方針：切断点と終点を含む。
規約：HA 1.3.1.6。使われ方：右成分の濃度条件。 -/
lemma right_two (hj : j ∈ I) (hb : b ∈ I) (hjb : j < b) :
    2 ≤ (I.filter (j ≤ ·)).card :=
  two_le_card (Finset.mem_filter.mpr ⟨hj, le_rfl⟩)
    (Finset.mem_filter.mpr ⟨hb, hjb.le⟩) (ne_of_lt hjb)

/-- 概要：左切断の最小元は元の最小元。方針：所属と下界性を継承する。
規約：HA 1.3.1.6。使われ方：合成の始点。 -/
lemma left_min (ha : IsLeast (I : Set α) a) (haj : a ≤ j)
    (h : (I.filter (· ≤ j)).Nonempty) : a = (I.filter (· ≤ j)).min' h := by
  symm
  apply (Finset.isLeast_min' _ h).unique
  exact ⟨Finset.mem_filter.mpr ⟨ha.1, haj⟩, fun _ hk => ha.2 (Finset.mem_filter.mp hk).1⟩

/-- 概要：左切断の最大元は切断点。方針：filter の上界条件を使う。
規約：HA 1.3.1.6。使われ方：左成分の終点。 -/
lemma left_max (hj : j ∈ I) (h : (I.filter (· ≤ j)).Nonempty) :
    j = (I.filter (· ≤ j)).max' h := by
  symm
  apply (Finset.isGreatest_max' _ h).unique
  exact ⟨Finset.mem_filter.mpr ⟨hj, le_rfl⟩, fun _ hk => (Finset.mem_filter.mp hk).2⟩

/-- 概要：右切断の最小元は切断点。方針：filter の下界条件を使う。
規約：HA 1.3.1.6。使われ方：右成分の始点。 -/
lemma right_min (hj : j ∈ I) (h : (I.filter (j ≤ ·)).Nonempty) :
    j = (I.filter (j ≤ ·)).min' h := by
  symm
  apply (Finset.isLeast_min' _ h).unique
  exact ⟨Finset.mem_filter.mpr ⟨hj, le_rfl⟩, fun _ hk => (Finset.mem_filter.mp hk).2⟩

/-- 概要：右切断の最大元は元の最大元。方針：所属と上界性を継承する。
規約：HA 1.3.1.6。使われ方：合成の終点。 -/
lemma right_max (hb : IsGreatest (I : Set α) b) (hjb : j ≤ b)
    (h : (I.filter (j ≤ ·)).Nonempty) : b = (I.filter (j ≤ ·)).max' h := by
  symm
  apply (Finset.isGreatest_max' _ h).unique
  exact ⟨Finset.mem_filter.mpr ⟨hb.1, hjb⟩, fun _ hk => hb.2 (Finset.mem_filter.mp hk).1⟩

/-- 概要：左右の切断の濃度和は元の濃度に一を足したもの。方針：和集合は I、共通部分は {j}。
規約：HA 1.3.1.6。使われ方：合成項の次数の和を計算する。 -/
lemma split_card (hj : j ∈ I) :
    (I.filter (· ≤ j)).card + (I.filter (j ≤ ·)).card = I.card + 1 := by
  have hu : I.filter (· ≤ j) ∪ I.filter (j ≤ ·) = I := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => h.elim And.left And.left, fun hk => (le_total k j).elim
      (fun h => Or.inl ⟨hk, h⟩) (fun h => Or.inr ⟨hk, h⟩)⟩
  have hi : I.filter (· ≤ j) ∩ I.filter (j ≤ ·) = {j} := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => le_antisymm h.1.2 h.2.2
    · rintro rfl
      exact ⟨⟨hj, le_rfl⟩, ⟨hj, le_rfl⟩⟩
  have h := Finset.card_union_add_card_inter (I.filter (· ≤ j)) (I.filter (j ≤ ·))
  rw [hu, hi, Finset.card_singleton] at h
  exact h.symm

/-- 概要：二点集合はその最小元と最大元からなる。
方針：異なる両端を含む二点部分集合との濃度比較。
規約：HA Construction 1.3.1.6。使われ方：退化辺の単位分岐。 -/
lemma eq_pair (hc : I.card = 2) (ha : IsLeast (I : Set α) a)
    (hb : IsGreatest (I : Set α) b) : I = {a, b} := by
  have hab : a < b := by
    have h := I.min'_lt_max'_of_card (by omega)
    have hmin := ha.unique (I.isLeast_min' ⟨a, ha.1⟩)
    have hmax := hb.unique (I.isGreatest_max' ⟨a, ha.1⟩)
    simpa only [← hmin, ← hmax] using h
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha.1
    · exact hb.1
  · simp [hc, ne_of_lt hab]

section Image

variable {β : Type*} [LinearOrder β] {f : α → β}

/-- 概要：単調写像の像の最小元は元の最小元の像。
方針：最小元の所属と下界性を写す。
規約：HA Construction 1.3.1.6。使われ方：単体の引き戻しの始点。 -/
lemma image_min (hf : Monotone f) (ha : IsLeast (I : Set α) a)
    (h : (I.image f).Nonempty) : f a = (I.image f).min' h := by
  symm
  apply (Finset.isLeast_min' _ h).unique
  refine ⟨Finset.mem_image.mpr ⟨a, ha.1, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact hf (ha.2 hx)

/-- 概要：単調写像の像の最大元は元の最大元の像。
方針：最大元の所属と上界性を写す。
規約：HA Construction 1.3.1.6。使われ方：単体の引き戻しの終点。 -/
lemma image_max (hf : Monotone f) (hb : IsGreatest (I : Set α) b)
    (h : (I.image f).Nonempty) : f b = (I.image f).max' h := by
  symm
  apply (Finset.isGreatest_max' _ h).unique
  refine ⟨Finset.mem_image.mpr ⟨b, hb.1, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact hf (hb.2 hx)

omit [LinearOrder α] in
/-- 概要：I 上単射な写像による像は二点以上という条件を保つ。
方針：像の濃度が元と等しいことを使う。
規約：HA Construction 1.3.1.6。使われ方：引き戻しの単射分岐の成分。 -/
lemma image_two (hf : Set.InjOn f (I : Set α)) (hI : 2 ≤ I.card) :
    2 ≤ (I.image f).card := by
  rw [Finset.card_image_of_injOn hf]
  exact hI

/-- 概要：I 上単射な写像は I に属する点の削除と可換。
方針：像の元の表示と I 上の単射性を使う。
規約：HA Construction 1.3.1.6。使われ方：引き戻しと削除項の比較。 -/
lemma image_erase (hf : Set.InjOn f (I : Set α)) (hj : j ∈ I) :
    (I.erase j).image f = (I.image f).erase (f j) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxj, hx⟩, rfl⟩
    exact ⟨fun h => hxj (hf hx hj h), ⟨x, hx, rfl⟩⟩
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨fun h => hy (congrArg f h), hx⟩, rfl⟩

/-- 概要：単調かつ I 上単射な写像は左右の順序比較を反映する。
方針：単調性と単射性から I 上の狭義単調性を得る。
規約：HA Construction 1.3.1.6。使われ方：内部点と切断の添字の移送。 -/
lemma image_le_iff (hf : Monotone f) (hi : Set.InjOn f (I : Set α))
    {x y : α} (hx : x ∈ I) (hy : y ∈ I) : f x ≤ f y ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    exact (not_lt_of_ge h)
      (((hf.monotoneOn (I : Set α)).strictMonoOn_of_injOn hi) hy hx (lt_of_not_ge hxy))
  · exact fun h => hf h

/-- 概要：単調かつ I 上単射な写像は狭義の順序比較を反映する。
方針：逆向きの非狭義比較の否定に帰着する。
規約：HA Construction 1.3.1.6。使われ方：内部点と符号の添字の移送。 -/
lemma image_lt_iff (hf : Monotone f) (hi : Set.InjOn f (I : Set α))
    {x y : α} (hx : x ∈ I) (hy : y ∈ I) : f x < f y ↔ x < y := by
  rw [lt_iff_not_ge, lt_iff_not_ge, image_le_iff hf hi hy hx]

/-- 概要：二点集合上で単射でない写像は両端を同じ点に写す。
方針：集合を両端の対で表示し、対上の単射性の判定を使う。
規約：HA Construction 1.3.1.6。使われ方：退化辺の単位の終点の同定。 -/
lemma collapse_two (hi : ¬ Set.InjOn f (I : Set α)) (hc : I.card = 2)
    (ha : IsLeast (I : Set α) a) (hb : IsGreatest (I : Set α) b) : f a = f b := by
  by_contra h
  apply hi
  rw [eq_pair hc ha hb]
  simpa using (Set.injOn_pair.mpr (fun he => (h he).elim) : Set.InjOn f {a, b})

/-- 概要：単調かつ I 上単射な写像は左切断と可換。
方針：像の表示と順序比較の反映を使う。
規約：HA Construction 1.3.1.6。使われ方：引き戻しの合成項の左因子。 -/
lemma image_left (hf : Monotone f) (hi : Set.InjOn f (I : Set α)) (hj : j ∈ I) :
    (I.filter (· ≤ j)).image f = (I.image f).filter (· ≤ f j) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hxj⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hf hxj⟩
  · rintro ⟨⟨x, hx, rfl⟩, hxj⟩
    exact ⟨x, ⟨hx, (image_le_iff hf hi hx hj).mp hxj⟩, rfl⟩

/-- 概要：単調かつ I 上単射な写像は右切断と可換。
方針：像の表示と順序比較の反映を使う。
規約：HA Construction 1.3.1.6。使われ方：引き戻しの合成項の右因子。 -/
lemma image_right (hf : Monotone f) (hi : Set.InjOn f (I : Set α)) (hj : j ∈ I) :
    (I.filter (j ≤ ·)).image f = (I.image f).filter (f j ≤ ·) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hjx⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, hf hjx⟩
  · rintro ⟨⟨x, hx, rfl⟩, hjx⟩
    exact ⟨x, ⟨hx, (image_le_iff hf hi hj hx).mp hjx⟩, rfl⟩

/-- 概要：内部点より右にある部分集合の像は、像の内部点より右にある部分集合。
方針：像の元の表示と狭義比較の反映を使う。
規約：HA Construction 1.3.1.6。使われ方：引き戻しの方程式の符号の比較。 -/
lemma image_strict_right (hf : Monotone f) (hi : Set.InjOn f (I : Set α)) (hj : j ∈ I) :
    (I.filter (j < ·)).image f = (I.image f).filter (f j < ·) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hjx⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (hf.monotoneOn (I : Set α)).strictMonoOn_of_injOn hi hj hx hjx⟩
  · rintro ⟨⟨x, hx, rfl⟩, hjx⟩
    exact ⟨x, ⟨hx, (image_lt_iff hf hi hj hx).mp hjx⟩, rfl⟩

/-- 概要：内部点より右にある点の数は像を取っても変わらない。
方針：右側部分集合の像の記述と、単射な像の濃度の等式を使う。
規約：HA Construction 1.3.1.6。使われ方：`Int.negOnePow` の指数を同定する。 -/
lemma image_sign_card (hf : Monotone f) (hi : Set.InjOn f (I : Set α)) (hj : j ∈ I) :
    ((I.image f).filter (f j < ·)).card = (I.filter (j < ·)).card := by
  rw [← image_strict_right hf hi hj]
  apply Finset.card_image_of_injOn
  exact hi.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1)

end Image

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index
