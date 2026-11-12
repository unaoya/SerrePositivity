module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-!
# Alexander–Whitney の切断の添字

概要：端点を含む左右の切断の非空性・次数・反復切断の式をまとめる。
方針：同じ切断点が左右に一度ずつ入ることと順序の推移性を使う。
規約：標準 DK 成分の次数は 1−|J|、切断点は両因子で共有する。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW 豊穣合成の添字計算。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

namespace AWIndex

variable {α : Type*} [LinearOrder α] {J : Finset α} {i j : α}

/-- 概要：集合の元で切った接頭部分は非空である。
方針：切断点自身が属する。
規約：両端の切断も許す。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の第一因子。 -/
lemma left_nonempty (hj : j ∈ J) : (J.filter (· ≤ j)).Nonempty :=
  ⟨j, Finset.mem_filter.mpr ⟨hj, le_rfl⟩⟩

/-- 概要：集合の元で切った接尾部分は非空である。
方針：切断点自身が属する。
規約：両端の切断も許す。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の第二因子。 -/
lemma right_nonempty (hj : j ∈ J) : (J.filter (j ≤ ·)).Nonempty :=
  ⟨j, Finset.mem_filter.mpr ⟨hj, le_rfl⟩⟩

/-- 概要：左右の切断の標準 DK 次数の和は元の次数である。
方針：切断の濃度和が元の濃度 +1 であることを使う。
規約：cochain 次数の等式として述べる。
使われ方：HA 1.3.1.13 の斉次合成の次数の証明。 -/
lemma degree_add (hj : j ∈ J) :
    (1 - ((J.filter (j ≤ ·)).card : ℤ)) + (1 - ((J.filter (· ≤ j)).card : ℤ)) =
      1 - (J.card : ℤ) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
  omega

/-- 概要：接頭部分をさらに手前で切ると最初から手前で切った集合になる。
方針：順序の推移性で余分な上界条件を除く。
規約：二つの切断点が等しい場合も含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の結合律。 -/
lemma left_left (hij : i ≤ j) : (J.filter (· ≤ j)).filter (· ≤ i) = J.filter (· ≤ i) := by
  ext a
  simp only [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hij⟩, h.2⟩⟩

/-- 概要：接尾部分をさらに後ろで切ると最初から後ろで切った集合になる。
方針：順序の推移性で余分な下界条件を除く。
規約：二つの切断点が等しい場合も含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW の結合律。 -/
lemma right_right (hij : i ≤ j) : (J.filter (i ≤ ·)).filter (j ≤ ·) = J.filter (j ≤ ·) := by
  ext a
  simp only [Finset.mem_filter]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hij.trans h.2⟩, h.2⟩⟩

/-- 概要：二つの切断の中間部分は接頭と接尾のどちらから切っても同じである。
方針：二つの filter の条件の順序を交換する。
規約：切断点の順序を仮定しない集合の等式。
使われ方：Kerodon 2.5.8（Tag 00S0） の三重合成の中間因子。 -/
lemma middle : (J.filter (· ≤ j)).filter (i ≤ ·) =
    (J.filter (i ≤ ·)).filter (· ≤ j) := by
  ext a
  simp only [Finset.mem_filter]
  tauto

end AWIndex

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
