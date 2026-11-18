module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotPositionOrder

/-!
模型。文献の定義との比較は後で
# 切断点色への挿入の全活動集合

概要：Berger–Fresse §2.2.6 の合成活動集合を外側残り位置と内側活動位置の像へ分ける。
方針：各像の活動性・単射性・前後の非交差性と全個数を合わせる。
規約：正の内側 arity と任意の内外語次数。
使われ方：切断点色分岐の合成逆転数を二ブロックの逆転数へ分ける。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：外側切断点以外の位置は切断点色と異なる（BF §2.2.1）。
方針：非零切断点の色の唯一性を使う。
規約：外側活動集合への所属は不要。
使われ方：残り活動位置を既存の残り位置写像で扱う。 -/
lemma remaining_color_ne_of_pivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k)
    (r : Fin (m + 1 + d)) (hr : r ≠ a.val.1) : u.val r ≠ k := by
  intro he
  exact hr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique a.property.1 r (he.trans hp.symm))

/-- 概要：内側位置写像は全位置上で単射（BF §2.2.6）。
方針：厳密順序の保存から単射性を得る。
規約：切断点色への挿入。
使われ方：内側活動集合の像の個数を保つ。 -/
lemma pivotInnerMap_injective (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k) :
    Function.Injective (a.pivotInnerMap hp) :=
  (show StrictMono (a.pivotInnerMap hp) from fun i j hij =>
    (a.pivotInnerMap_lt_iff hp i j).2 hij).injective

/-- 概要：外側の残り活動位置は全内側位置より前（BF §2.2.6）。
方針：全外側活動位置が切断点以下であることと前方残り位置の順序を使う。
規約：外側の切断点自体を活動集合から除く。
使われ方：二つの活動像の非交差性と交差逆転の向き。 -/
lemma remainingPositionMap_pivot_order (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k)
    (r : Fin (m + 1 + d)) (hr : r ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1)
    (j : Fin (n + e)) : a.remainingPositionMap r < a.pivotInnerMap hp j := by
  have hr' := Finset.mem_erase.mp hr
  have hrk := a.remaining_color_ne_of_pivot hp r hr'.1
  rw [a.remainingPositionMap_of_ne r hrk]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt_inner u v k a.partition _ a.val.1 hp r hrk
    (lt_of_le_of_ne (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot a.property.1 hr'.2) hr'.1) j

/-- 概要：残り位置写像は切断点を除いた外側活動集合上で単射（BF §2.2.6）。
方針：残り活動色は指定色と異なり、その位置間の厳密順序を保持する。
規約：切断点色への挿入。
使われ方：外側残り活動像の個数を保つ。 -/
lemma remainingPositionMap_pivot_injOn (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hp : u.val a.val.1 = k) :
    Set.InjOn a.remainingPositionMap ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1) := by
  intro r hr s hs he
  have hrk := a.remaining_color_ne_of_pivot hp r (Finset.mem_erase.mp hr).1
  have hsk := a.remaining_color_ne_of_pivot hp s (Finset.mem_erase.mp hs).1
  rcases lt_trichotomy r s with h | h | h
  · exact False.elim ((ne_of_lt ((a.remainingPositionMap_lt_iff r s hrk hsk).2 h)) he)
  · exact h
  · exact False.elim ((ne_of_lt ((a.remainingPositionMap_lt_iff s r hsk hrk).2 h)) he.symm)

/-- 概要：内側活動位置は合成語の活動位置へ写る（BF §2.2.6）。
方針：挿入色の辺出力の保存と内側切断点以下の順序を使う。
規約：内側辺切断点を some q として指定する。
使われ方：全内側活動像が合成活動集合に入ること。 -/
lemma pivotInnerMap_mem_active (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hp : u.val a.val.1 = k) (q : Fin (n + e)) (ha : a.val.2 = some q)
    (j : Fin (n + e)) (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) :
    a.pivotInnerMap hp j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      a.compositePosition := by
  have H := a.property.2
  rw [ha] at H
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_activePositions_iff_output_and_le _ _ (a.compositePosition_nondegenerate hn) _).2
  constructor
  · rw [a.pivotInnerMap_value hn hp, a.compositePosition_pivot_inserted_output hn q ha hp]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff v q H.2 _).2 ⟨j, hj, rfl⟩
  · have hm : StrictMono (a.pivotInnerMap hp) := fun i j hij =>
      (a.pivotInnerMap_lt_iff hp i j).2 hij
    have hle := hm.monotone (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot H.2 hj)
    rwa [a.pivotInnerMap_at_cut hp q ha] at hle

/-- 概要：切断点を除いた外側活動位置は合成活動位置へ写る（BF §2.2.6）。
方針：残り色の辺出力を保持し、全内側位置より前であることを使う。
規約：切断点色への内側辺作用。
使われ方：全外側残り活動像が合成活動集合に入ること。 -/
lemma remainingPositionMap_pivot_mem_active (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hp : u.val a.val.1 = k) (q : Fin (n + e)) (ha : a.val.2 = some q)
    (r : Fin (m + 1 + d)) (hr : r ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1) :
    a.remainingPositionMap r ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      a.compositePosition := by
  have hr' := Finset.mem_erase.mp hr
  have hrk := a.remaining_color_ne_of_pivot hp r hr'.1
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_activePositions_iff_output_and_le _ _ (a.compositePosition_nondegenerate hn) _).2
  constructor
  · rw [a.remainingPositionMap_of_ne r hrk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition,
      a.compositePosition_remaining_output hn]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u a.val.1 a.property.1 _).2 ⟨r, hr'.2, rfl⟩
  · have hlt := a.remainingPositionMap_pivot_order hp r hr q
    rw [a.pivotInnerMap_at_cut hp q ha] at hlt
    exact hlt.le

/-- 概要：合成活動集合は外側残り活動像と内側活動像の非交差な和（BF §2.2.6）。
方針：両像の活動性と単射性、前後の厳密順序、全個数を比較する。
規約：正の内側 arity、全内外語次数。
使われ方：合成逆転数の二ブロック分解。 -/
lemma activePositions_pivot_union (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hp : u.val a.val.1 = k) (q : Fin (n + e)) (ha : a.val.2 = some q) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1).image a.remainingPositionMap ∪
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q).image (a.pivotInnerMap hp) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  have H := a.property.2
  rw [ha] at H
  have hd : Disjoint
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1).image a.remainingPositionMap)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q).image (a.pivotInnerMap hp)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hj'
    exact (ne_of_lt (a.remainingPositionMap_pivot_order hp r hr s)) hs.symm
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
      exact a.remainingPositionMap_pivot_mem_active hn hp q ha r hr
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
      exact a.pivotInnerMap_mem_active hn hp q ha r hr
  · rw [Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injOn (a.remainingPositionMap_pivot_injOn hp),
      Finset.card_image_of_injective _ (a.pivotInnerMap_injective hp),
      Finset.card_erase_of_mem (show a.val.1 ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1 from
        Finset.mem_insert_self _ _),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card u a.val.1 a.property.1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card v q H.2,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card _ _ (a.compositePosition_nondegenerate hn)]
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
