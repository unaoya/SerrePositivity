module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Sign
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Finset.Card

/-!
# 削除境界の標準座標への符号変換

概要：N4 の上側の点の数による係数を、標準境界の下側の点の数による係数へ変換する。
方針：削除する点の前後の濃度和と次数符号の漸化式を使う。
規約：全ての有限線形順序集合で扱う。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の標準 chain map 方程式の回収。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：所属点の前と後の点数の和に一を足すと元の集合の濃度になる。
方針：二つの filter の非交和を点の削除に同定する。
規約：削除点の所属を明示する。
使われ方：HA 1.3.1.12 の二通りの削除符号の比較。 -/
lemma card_before_add_after {α : Type*} [LinearOrder α] (J : Finset α) (j : α) (hj : j ∈ J) :
    (J.filter (· < j)).card + (J.filter (j < ·)).card + 1 = J.card := by
  have hu : J.filter (· < j) ∪ J.filter (j < ·) = J.erase j := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
      · exact ⟨ne_of_lt h, hx⟩
      · exact ⟨ne_of_gt h, hx⟩
    · rintro ⟨hne, hx⟩
      exact (lt_or_gt_of_ne hne).elim (fun h ↦ Or.inl ⟨hx, h⟩)
        (fun h ↦ Or.inr ⟨hx, h⟩)
  have hd : Disjoint (J.filter (· < j)) (J.filter (j < ·)) :=
    Finset.disjoint_left.mpr fun x hx hy ↦
      lt_asymm (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  have hc := Finset.card_union_of_disjoint hd
  rw [hu] at hc
  have he := Finset.card_erase_add_one hj
  omega

/-- 概要：自然数に一を加えた指数の negOnePow の整数値は通常のべきである。
方針：整数へのキャストと自然数べきの既存の比較を使う。
規約：N4 の係数は整数単元で与えられる。
使われ方：HA 1.3.1.12 の整数スカラーとしての係数の計算。 -/
lemma negOnePow_nat_add_one (k : ℕ) :
    (((k : ℤ) + 1).negOnePow : ℤ) = (-1 : ℤ) ^ (k + 1) := by
  simpa only [Nat.cast_add, Nat.cast_one] using Int.coe_negOnePow_natCast (k + 1)

/-- 概要：次数符号を掛けた N4 の削除係数は標準境界係数と削除後の次数符号の積になる。
方針：前後の濃度和、次数符号の微分則、符号の平方が一であることを使う。
規約：元の集合は二点以上、削除点はその集合に属する。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の標準 DK 座標への全成分の変換。 -/
lemma degreeSign_deletion {α : Type*} [LinearOrder α] (J : Finset α) (j : α)
    (hJ : 2 ≤ J.card) (hj : j ∈ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) *
      ((((J.filter (j < ·)).card : ℤ) + 1).negOnePow : ℤ) =
        (-1 : ℤ) ^ (J.filter (· < j)).card * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign ((J.erase j).card - 1) := by
  rw [negOnePow_nat_add_one]
  have hc := card_before_add_after J j hj
  have he := Finset.card_erase_add_one hj
  have hs : (J.erase j).card - 1 = J.card - 2 := by omega
  rw [hs]
  have hp : (-1 : ℤ) ^ (J.filter (· < j)).card *
      (-1 : ℤ) ^ ((J.filter (j < ·)).card + 1) = (-1 : ℤ) ^ J.card := by
    rw [← pow_add]
    congr 1
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) * (-1 : ℤ) ^ J.card = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 2) := by
    have h1 : J.card - 2 + 1 = J.card - 1 := by omega
    have h2 : J.card - 2 + 2 = J.card := by omega
    simpa only [h1, h2] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign_differential (J.card - 2)
  have hsq : (-1 : ℤ) ^ (J.filter (· < j)).card *
      (-1 : ℤ) ^ (J.filter (· < j)).card = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1 : ℤ) ^ (J.filter (· < j)).card *
        (-1 : ℤ) ^ (J.filter (· < j)).card) *
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) * (-1 : ℤ) ^ ((J.filter (j < ·)).card + 1)) := by
      rw [hsq, one_mul]
    _ = (-1 : ℤ) ^ (J.filter (· < j)).card *
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) *
          ((-1 : ℤ) ^ (J.filter (· < j)).card *
            (-1 : ℤ) ^ ((J.filter (j < ·)).card + 1))) := by ring
    _ = _ := by rw [hp, hd]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
