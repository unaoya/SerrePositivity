module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedCuts

/-! # 右 pinched 線形化における二番目の点

概要：二点以上の有限集合で二番目の点と、その左右の切断を計算する。
方針：最小点を消した集合の最小点を使い、単位の合成が現れる唯一の切断を記述する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：最小点の削除項の復元。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：二点以上の有限集合の二番目の点。
方針：最小点を消した非空集合の最小点を取る。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単位との合成が残る切断点。 -/
def second {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) : Fin (n + 1) :=
  (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))).min' (by
    apply Finset.card_pos.mp
    have := Finset.card_erase_add_one (J.min'_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    omega)

/-- 概要：二番目の点は最小点を消した集合に属する。
方針：非空有限集合の最小点の所属を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：二番目の点の所属と最小点との相異。 -/
lemma second_mem_erase {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    second J hJ ∈ J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) := Finset.min'_mem _ _

/-- 概要：最小点は二番目の点より真に小さい。
方針：最小性と、最小点を消した集合への所属を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：内部切断点としての二番目の点。 -/
lemma first_lt_second {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) < second J hJ := by
  have hs := Finset.mem_erase.mp (second_mem_erase J hJ)
  exact lt_of_le_of_ne ((J.isLeast_min' _).2 hs.2) hs.1.symm

/-- 概要：二番目の点までの左切断は最初の二点だけからなる。
方針：最小点以外の左切断の点に、削除後の最小性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面の単位成分が残る場合の判定。 -/
lemma left_second {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    J.filter (· ≤ second J hJ) = {J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ), second J hJ} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, his⟩
    by_cases hf : i = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
    · exact Or.inl hf
    · right
      exact le_antisymm his (((J.erase _).isLeast_min' _).2 (Finset.mem_erase.mpr ⟨hf, hi⟩))
  · rintro (rfl | rfl)
    · exact ⟨J.min'_mem _, (first_lt_second J hJ).le⟩
    · exact ⟨(Finset.mem_erase.mp (second_mem_erase J hJ)).2, le_rfl⟩

/-- 概要：二番目の点からの右切断は最小点を消した集合。
方針：最小点を消した集合の最小性を両方向に使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単位と合成する右成分は最初の削除成分。 -/
lemma right_second {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    J.filter (second J hJ ≤ ·) = J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hi, hsi⟩
    refine ⟨?_, hi⟩
    intro he
    subst i
    exact (not_le_of_gt (first_lt_second J hJ)) hsi
  · rintro ⟨hf, hi⟩
    exact ⟨hi, ((J.erase _).isLeast_min' _).2 (Finset.mem_erase.mpr ⟨hf, hi⟩)⟩

/-- 概要：最小点より大きい点の集合は最小点の削除。
方針：最小性により、所属する非最小点は真に大きい。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：最初の削除項の符号の計算。 -/
lemma above_first {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    J.filter (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) < ·) = J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hi, hfi⟩
    exact ⟨ne_of_gt hfi, hi⟩
  · rintro ⟨hf, hi⟩
    exact ⟨hi, lt_of_le_of_ne ((J.isLeast_min' _).2 hi) hf.symm⟩

/-- 概要：二番目の点より大きい点の集合は最初の二点の削除。
方針：最小点を消した集合の最小性と、二番目の点との相異を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単位の合成項の符号の計算。 -/
lemma above_second {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    J.filter (second J hJ < ·) = (J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))).erase (second J hJ) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hi, hsi⟩
    exact ⟨ne_of_gt hsi, ne_of_gt ((first_lt_second J hJ).trans hsi), hi⟩
  · rintro ⟨hs, hf, hi⟩
    exact ⟨hi, lt_of_le_of_ne (((J.erase _).isLeast_min' _).2
      (Finset.mem_erase.mpr ⟨hf, hi⟩)) hs.symm⟩

/-- 概要：二番目の点の削除係数は最小点の削除係数の逆符号。
方針：二つの厳密右切断の濃度が一異なることと整数の negOnePow の加法則を使う。
規約：Kerodon §4.6.5（Tag 01KW）、N0.3 の cochain 符号。使われ方：合成項の負号を最初の削除係数へ直す。 -/
lemma sign_second {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) :
    (((J.filter (second J hJ < ·)).card : ℤ) + 1).negOnePow =
      -(((J.filter (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) < ·)).card : ℤ) + 1).negOnePow := by
  rw [above_first J hJ, above_second J hJ]
  have hs := Finset.card_erase_add_one (second_mem_erase J hJ)
  have he : ((J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))).card : ℤ) + 1 =
      ((((J.erase (J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))).erase (second J hJ)).card : ℤ) + 1) + 1 := by
    omega
  rw [he]
  simp only [Int.negOnePow_add, Int.negOnePow_one, mul_neg_one, neg_neg]

/-- 概要：内部点までの左切断が二点となるのは、その点が二番目の点である場合に限る。
方針：二点集合を両端で記述し、二番目の点の最小性を使う。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：合成項のうち単位以外が全て零になることの判定。 -/
lemma left_card_two_iff {n : ℕ} (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card)
    (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) < j) :
    (J.filter (· ≤ j)).card = 2 ↔ j = second J hJ := by
  constructor
  · intro hc
    have he : J.filter (· ≤ j) = {J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ), j} :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.eq_pair hc
        ⟨Finset.mem_filter.mpr ⟨J.min'_mem _, haj.le⟩,
          fun _ ht => (J.isLeast_min' _).2 (Finset.mem_filter.mp ht).1⟩
        ⟨Finset.mem_filter.mpr ⟨hj, le_rfl⟩, fun _ ht => (Finset.mem_filter.mp ht).2⟩
    have hs : second J hJ ∈ J.filter (· ≤ j) :=
      Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (second_mem_erase J hJ)).2,
        ((J.erase _).isLeast_min' _).2 (Finset.mem_erase.mpr ⟨ne_of_gt haj, hj⟩)⟩
    rw [he] at hs
    rcases Finset.mem_insert.mp hs with hs | hs
    · exact False.elim ((ne_of_gt (first_lt_second J hJ)) hs)
    · exact (Finset.mem_singleton.mp hs).symm
  · rintro rfl
    rw [left_second]
    exact Finset.card_pair (ne_of_lt (first_lt_second J hJ))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
