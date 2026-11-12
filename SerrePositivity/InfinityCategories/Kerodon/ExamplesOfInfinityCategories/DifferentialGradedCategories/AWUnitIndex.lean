module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWConstant

/-!
# AW 単位則の端点の切断

概要：最小点・最大点での切断を計算し、他の切断の非自明な側は二点以上となることを示す。
方針：最小点・最大点と切断点を切断集合に含める。
規約：一点集合も端点の計算に含む。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW の単位則の和の消去。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

variable {α : Type*} [LinearOrder α] {J : Finset α}

/-- 概要：最小点での接頭部分はその一点である。
方針：最小点の下界性と上界条件を合わせる。
規約：非空集合で述べる。
使われ方：Kerodon 2.5.8（Tag 00S0） の後の射の単位の評価。 -/
lemma left_at_min (hJ : J.Nonempty) : J.filter (· ≤ J.min' hJ) = {J.min' hJ} := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro h
    exact le_antisymm h.2 (J.min'_le a h.1)
  · rintro rfl
    exact ⟨J.min'_mem hJ, le_rfl⟩

/-- 概要：最小点での接尾部分は元の集合である。
方針：全ての元が最小点以上であることを使う。
規約：非空集合で述べる。
使われ方：Kerodon 2.5.8（Tag 00S0） の後の射の単位との合成の値。 -/
lemma right_at_min (hJ : J.Nonempty) : J.filter (J.min' hJ ≤ ·) = J := by
  ext a
  simp only [Finset.mem_filter, and_iff_left_iff_imp]
  exact J.min'_le a

/-- 概要：最大点での接頭部分は元の集合である。
方針：全ての元が最大点以下であることを使う。
規約：非空集合で述べる。
使われ方：Kerodon 2.5.8（Tag 00S0） の前の射の単位との合成の値。 -/
lemma left_at_max (hJ : J.Nonempty) : J.filter (· ≤ J.max' hJ) = J := by
  ext a
  simp only [Finset.mem_filter, and_iff_left_iff_imp]
  exact J.le_max' a

/-- 概要：最大点での接尾部分はその一点である。
方針：最大点の上界性と下界条件を合わせる。
規約：非空集合で述べる。
使われ方：Kerodon 2.5.8（Tag 00S0） の前の射の単位の評価。 -/
lemma right_at_max (hJ : J.Nonempty) : J.filter (J.max' hJ ≤ ·) = {J.max' hJ} := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · intro h
    exact le_antisymm (J.le_max' a h.1) h.2
  · rintro rfl
    exact ⟨J.max'_mem hJ, le_rfl⟩

/-- 概要：最小点以外での接頭部分は二点以上である。
方針：最小点と切断点が異なる二点として属する。
規約：切断点も元の集合に属するとする。
使われ方：Kerodon 2.5.8（Tag 00S0） の後の射が単位である非端点項の消滅。 -/
lemma left_two_of_ne_min (hJ : J.Nonempty) {j : α} (hj : j ∈ J) (hne : j ≠ J.min' hJ) :
    2 ≤ (J.filter (· ≤ j)).card := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.two_le_card (a := J.min' hJ) (b := j)
  · exact Finset.mem_filter.mpr ⟨J.min'_mem hJ, J.min'_le j hj⟩
  · exact Finset.mem_filter.mpr ⟨hj, le_rfl⟩
  · exact hne.symm

/-- 概要：最大点以外での接尾部分は二点以上である。
方針：切断点と最大点が異なる二点として属する。
規約：切断点も元の集合に属するとする。
使われ方：Kerodon 2.5.8（Tag 00S0） の前の射が単位である非端点項の消滅。 -/
lemma right_two_of_ne_max (hJ : J.Nonempty) {j : α} (hj : j ∈ J) (hne : j ≠ J.max' hJ) :
    2 ≤ (J.filter (j ≤ ·)).card := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.two_le_card (a := j) (b := J.max' hJ)
  · exact Finset.mem_filter.mpr ⟨hj, le_rfl⟩
  · exact Finset.mem_filter.mpr ⟨J.max'_mem hJ, J.le_max' j hj⟩
  · exact hne

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
