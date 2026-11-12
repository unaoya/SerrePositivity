module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-! # 基本退化写像の部分集合の計算

概要：隣接する二点だけを潰す写像について、単射性・削除・符号を計算する。
方針：`Fin.predAbove` の二つの右逆から、片方を除いた部分集合上の単射性を得る。
規約：HA Construction 1.3.1.6、基本退化は `SimplexCategory.σ`。
使われ方：退化単体の方程式で残る二項の相殺。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：相異なる三点を含む有限集合の濃度は三以上。
方針：三点集合との包含による濃度比較。
規約：HA Construction 1.3.1.6。使われ方：非単射の高次成分が零となる条件。 -/
lemma three_le_card {α : Type*} [LinearOrder α] {J : Finset α} {x y z : α}
    (hx : x ∈ J) (hy : y ∈ J) (hz : z ∈ J) (hxy : x < y) (hyz : y < z) :
    3 ≤ J.card := by
  have h : ({x, y, z} : Finset α) ⊆ J := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  simpa [ne_of_lt hxy, ne_of_lt hyz, ne_of_lt (hxy.trans hyz)] using Finset.card_le_card h

variable {n : ℕ} (i : Fin (n + 1))

/-- 概要：左の重複点を除いた集合上で基本退化写像は単射。
方針：`succAbove_predAbove` で元を復元する。
規約：HA Construction 1.3.1.6。使われ方：左重複点を消した成分の評価。 -/
lemma predAbove_injOn_of_not_left {J : Finset (Fin (n + 2))} (hi : i.castSucc ∉ J) :
    Set.InjOn i.predAbove (J : Set (Fin (n + 2))) := by
  intro x hx y hy h
  have hx' : x ≠ i.castSucc := fun he => hi (he ▸ hx)
  have hy' : y ≠ i.castSucc := fun he => hi (he ▸ hy)
  have he := congrArg i.castSucc.succAbove h
  simpa only [Fin.succAbove_predAbove hx', Fin.succAbove_predAbove hy'] using he

/-- 概要：右の重複点を除いた集合上で基本退化写像は単射。
方針：`succ_succAbove_predAbove` で元を復元する。
規約：HA Construction 1.3.1.6。使われ方：右重複点を消した成分の評価。 -/
lemma predAbove_injOn_of_not_right {J : Finset (Fin (n + 2))} (hi : i.succ ∉ J) :
    Set.InjOn i.predAbove (J : Set (Fin (n + 2))) := by
  intro x hx y hy h
  have hx' : x ≠ i.succ := fun he => hi (he ▸ hx)
  have hy' : y ≠ i.succ := fun he => hi (he ▸ hy)
  have he := congrArg i.succ.succAbove h
  simpa only [Fin.succ_succAbove_predAbove hx', Fin.succ_succAbove_predAbove hy'] using he

/-- 概要：基本退化写像が部分集合上単射であるのは重複点の少なくとも片方を含まないとき。
方針：重複点の像は等しく、片方を除けば右逆により単射である。
規約：HA Construction 1.3.1.6。使われ方：退化の方程式の単射・非単射の分類。 -/
lemma predAbove_injOn_iff (J : Finset (Fin (n + 2))) :
    Set.InjOn i.predAbove (J : Set (Fin (n + 2))) ↔ ¬ (i.castSucc ∈ J ∧ i.succ ∈ J) := by
  constructor
  · intro h hpq
    have he := h hpq.1 hpq.2 (by simp)
    exact (ne_of_lt (Fin.castSucc_lt_succ (i := i))) he
  · intro h
    by_cases hp : i.castSucc ∈ J
    · exact predAbove_injOn_of_not_right i (fun hq => h ⟨hp, hq⟩)
    · exact predAbove_injOn_of_not_left i hp

/-- 概要：重複する二点の一方を消した像は、他方を消した像と等しい。
方針：重複点の像が等しいことにより像の元の表示を置き換える。
規約：HA Construction 1.3.1.6。使われ方：相殺する二つの削除項の同定。 -/
lemma predAbove_image_erase (J : Finset (Fin (n + 2)))
    (hp : i.castSucc ∈ J) (hq : i.succ ∈ J) :
    (J.erase i.castSucc).image i.predAbove = (J.erase i.succ).image i.predAbove := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases h : x = i.succ
    · subst x
      apply Finset.mem_image.mpr
      exact ⟨i.castSucc, Finset.mem_erase.mpr ⟨ne_of_lt Fin.castSucc_lt_succ, hp⟩, by simp⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨h, (Finset.mem_erase.mp hx).2⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases h : x = i.castSucc
    · subst x
      apply Finset.mem_image.mpr
      exact ⟨i.succ, Finset.mem_erase.mpr ⟨ne_of_gt Fin.castSucc_lt_succ, hq⟩, by simp⟩
    · exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨h, (Finset.mem_erase.mp hx).2⟩, rfl⟩

/-- 概要：隣接する重複点の右側点数は一だけ異なる。
方針：左点より大きい部分集合は、右点より大きい部分集合に右点を挿入したもの。
規約：HA Construction 1.3.1.6。使われ方：二つの削除項の符号が逆であること。 -/
lemma predAbove_sign_card (J : Finset (Fin (n + 2))) (hq : i.succ ∈ J) :
    (J.filter (i.castSucc < ·)).card = (J.filter (i.succ < ·)).card + 1 := by
  have he : J.filter (i.castSucc < ·) = insert i.succ (J.filter (i.succ < ·)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff, Fin.lt_def,
      Fin.val_castSucc, Fin.val_succ]
    constructor
    · rintro ⟨hx, hlt⟩
      by_cases he : x.val = i.val + 1
      · exact Or.inl he
      · exact Or.inr ⟨hx, by omega⟩
    · rintro (he | ⟨hx, hlt⟩)
      · have hx : x = i.succ := Fin.ext he
        subst x
        exact ⟨hq, by omega⟩
      · exact ⟨hx, by omega⟩
  rw [he, Finset.card_insert_of_notMem]
  simp

/-- 概要：相異なる二点の像が同じなら、その二点を含む集合上で写像は非単射。
方針：単射性をその二点に適用して矛盾を得る。
規約：HA Construction 1.3.1.6。使われ方：零となる退化成分を判定する。 -/
lemma not_injOn_of_equal {α β : Type*} {J : Finset α} {f : α → β} {p q : α}
    (hp : p ∈ J) (hq : q ∈ J) (hpq : p ≠ q) (he : f p = f q) :
    ¬ Set.InjOn f (J : Set α) := fun hi => hpq (hi hp hq he)

/-- 概要：重複点以外の内部点を消しても三点以上残る。
方針：左端が左重複点より小さければ左端と重複二点を使い、それ以外では右端を使う。
規約：HA Construction 1.3.1.6。使われ方：退化の削除項が零になる濃度条件。 -/
lemma erase_three_of_internal (J : Finset (Fin (n + 2))) {a b j : Fin (n + 2)}
    (ha : IsLeast (J : Set (Fin (n + 2))) a) (hb : IsGreatest (J : Set (Fin (n + 2))) b)
    (hp : i.castSucc ∈ J) (hq : i.succ ∈ J) (haj : a < j) (hjb : j < b)
    (hjp : j ≠ i.castSucc) (hjq : j ≠ i.succ) : 3 ≤ (J.erase j).card := by
  have hap := ha.2 hp
  have hqb := hb.2 hq
  have hp' : i.castSucc ∈ J.erase j := Finset.mem_erase.mpr ⟨hjp.symm, hp⟩
  have hq' : i.succ ∈ J.erase j := Finset.mem_erase.mpr ⟨hjq.symm, hq⟩
  by_cases h : a = i.castSucc
  · have hqb' : i.succ < b := by
      simp only [h, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at haj hjb hjp hjq ⊢
      omega
    exact three_le_card hp' hq' (Finset.mem_erase.mpr ⟨ne_of_gt hjb, hb.1⟩)
      Fin.castSucc_lt_succ hqb'
  · have hap' : a < i.castSucc := lt_of_le_of_ne hap h
    exact three_le_card (Finset.mem_erase.mpr ⟨ne_of_lt haj, ha.1⟩) hp' hq'
      hap' Fin.castSucc_lt_succ

/-- 概要：左重複点が最小元なら、右重複点までの左切断は重複二点の対。
方針：隣接する整数の間に頂点はないことを使う。
規約：HA Construction 1.3.1.6。使われ方：始点に接する退化の単位成分。 -/
lemma predAbove_left_of_min (J : Finset (Fin (n + 2)))
    (ha : IsLeast (J : Set (Fin (n + 2))) i.castSucc) (hq : i.succ ∈ J) :
    J.filter (· ≤ i.succ) = {i.castSucc, i.succ} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxq⟩
    have hpx : i.val ≤ x.val := ha.2 hx
    have hxq' : x.val ≤ i.val + 1 := hxq
    by_cases h : x.val = i.val
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (show x.val = i.val + 1 by omega))
  · rintro (rfl | rfl)
    · exact ⟨ha.1, Fin.castSucc_lt_succ.le⟩
    · exact ⟨hq, le_rfl⟩

/-- 概要：左重複点が最小元なら、右重複点からの右切断は左重複点を消した集合。
方針：最小元以外の頂点はその次の頂点以上である。
規約：HA Construction 1.3.1.6。使われ方：始点での削除項と合成項の同定。 -/
lemma predAbove_right_of_min (J : Finset (Fin (n + 2)))
    (ha : IsLeast (J : Set (Fin (n + 2))) i.castSucc) :
    J.filter (i.succ ≤ ·) = J.erase i.castSucc := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hx, hqx⟩
    exact ⟨ne_of_gt (Fin.castSucc_lt_succ.trans_le hqx), hx⟩
  · rintro ⟨hxp, hx⟩
    have hpx : i.val ≤ x.val := ha.2 hx
    have hne : x.val ≠ i.val := fun h => hxp (Fin.ext h)
    exact ⟨hx, show i.val + 1 ≤ x.val by omega⟩

/-- 概要：右重複点が最大元なら、左重複点からの右切断は重複二点の対。
方針：隣接する整数の間に頂点はないことを使う。
規約：HA Construction 1.3.1.6。使われ方：終点に接する退化の単位成分。 -/
lemma predAbove_right_of_max (J : Finset (Fin (n + 2)))
    (hp : i.castSucc ∈ J) (hb : IsGreatest (J : Set (Fin (n + 2))) i.succ) :
    J.filter (i.castSucc ≤ ·) = {i.castSucc, i.succ} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hpx⟩
    have hxq : x.val ≤ i.val + 1 := hb.2 hx
    have hpx' : i.val ≤ x.val := hpx
    by_cases h : x.val = i.val
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (show x.val = i.val + 1 by omega))
  · rintro (rfl | rfl)
    · exact ⟨hp, le_rfl⟩
    · exact ⟨hb.1, Fin.castSucc_lt_succ.le⟩

/-- 概要：右重複点が最大元なら、左重複点までの左切断は右重複点を消した集合。
方針：最大元と異なる頂点はその直前の頂点以下である。
規約：HA Construction 1.3.1.6。使われ方：終点での削除項と合成項の同定。 -/
lemma predAbove_left_of_max (J : Finset (Fin (n + 2)))
    (hb : IsGreatest (J : Set (Fin (n + 2))) i.succ) :
    J.filter (· ≤ i.castSucc) = J.erase i.succ := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hx, hxp⟩
    exact ⟨ne_of_lt (hxp.trans_lt Fin.castSucc_lt_succ), hx⟩
  · rintro ⟨hxq, hx⟩
    have hxq' : x.val ≤ i.val + 1 := hb.2 hx
    have hne : x.val ≠ i.val + 1 := fun h => hxq (Fin.ext h)
    exact ⟨hx, show x.val ≤ i.val by omega⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
