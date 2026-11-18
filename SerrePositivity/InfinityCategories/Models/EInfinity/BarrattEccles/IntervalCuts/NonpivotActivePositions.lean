module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotPositionOrder

/-!
模型。文献の定義との比較は後で
# 二出現色への挿入の全活動集合

概要：Berger–Fresse §2.2.6 の合成活動集合で最初の指定出現を内側活動列へ置き換える。
方針：残り外側像と内側像の活動性・単射性・非交差性と全個数を合わせる。
規約：正の内側 arity と任意の内外語次数。
使われ方：二出現色分岐の合成逆転数の両向き交差公式。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

local notation "r₀" => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k (Fin.mk 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k))

/-- 概要：残り位置写像は非指定色の外側切断点を合成切断点へ送る（BF §2.2.6）。
方針：切断点の非指定色分岐を評価する。
規約：内側頂点・辺の双方で成立。
使われ方：各像の合成切断点以下の条件。 -/
lemma remainingPositionMap_at_nonpivot_cut (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (hp : u.val a.val.1 ≠ k) : a.remainingPositionMap a.val.1 = a.compositePosition := by
  rw [a.remainingPositionMap_of_ne a.val.1 hp]
  exact (a.compositePosition_nonpivot_eq_outer hp).symm

/-- 概要：残り位置写像は最初の指定出現を除く外側活動集合上で単射（BF §2.2.6）。
方針：残り活動色の非指定色性と位置間の厳密順序を使う。
規約：二出現色分岐。
使われ方：外側残り活動像の個数を保つ。 -/
lemma remainingPositionMap_nonpivot_injOn (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    Set.InjOn a.remainingPositionMap ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀) := by
  intro r hr s hs he
  have hrk := a.remaining_color_ne_of_nonpivot q ha hp r hr
  have hsk := a.remaining_color_ne_of_nonpivot q ha hp s hs
  rcases lt_trichotomy r s with h | h | h
  · exact False.elim ((ne_of_lt ((a.remainingPositionMap_lt_iff r s hrk hsk).2 h)) he)
  · exact h
  · exact False.elim ((ne_of_lt ((a.remainingPositionMap_lt_iff s r hsk hrk).2 h)) he.symm)

/-- 概要：内側位置写像は内側活動集合上で単射（BF §2.2.6）。
方針：全活動位置が切断点以下であり、共通の前置長だけずれることを使う。
規約：活動集合の外の値は使わない。
使われ方：内側活動像の個数を保つ。 -/
lemma nonpivotInnerMap_injOn (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    Set.InjOn (a.nonpivotInnerMap q ha hp) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) := by
  have H := a.property.2
  rw [ha] at H
  intro i hi j hj he
  have hv := congrArg Fin.val he
  rw [a.nonpivotInnerMap_val q ha hp i (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot H.2 hi),
    a.nonpivotInnerMap_val q ha hp j (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot H.2 hj)] at hv
  exact Fin.ext (by omega)

/-- 概要：全内側活動位置は合成活動位置へ写る（BF §2.2.6）。
方針：挿入色の辺出力を保持し、最初の指定出現の部分語全体が合成切断点より前にあることを使う。
規約：二出現色分岐の正の内側 arity。
使われ方：内側活動像の合成活動集合への包含。 -/
lemma nonpivotInnerMap_mem_active (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) (j : Fin (n + e))
    (hj : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) :
    a.nonpivotInnerMap q ha hp j ∈
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  have H := a.property.2
  rw [ha] at H
  have hjq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot H.2 hj
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_activePositions_iff_output_and_le _ _ (a.compositePosition_nondegenerate hn) _).2
  constructor
  · rw [a.nonpivotInnerMap_value hn q ha hp j hjq,
      a.compositePosition_nonpivot_inserted_output hn q ha hp]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff v q H.2 _).2 ⟨j, hj, rfl⟩
  · have hlt := a.nonpivotInnerMap_lt_remainingPositionMap q ha hp a.val.1 hp
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.caesura_before_pivot a.property.1 (a.nonpivot_first_caesura q ha hp)) j hjq
    rw [a.remainingPositionMap_at_nonpivot_cut hp] at hlt
    exact hlt.le

/-- 概要：最初の指定出現以外の外側活動位置は合成活動位置へ写る（BF §2.2.6）。
方針：残り色の辺出力と残り位置間の順序を保つ。
規約：二出現色分岐の正の内側 arity。
使われ方：外側残り活動像の合成活動集合への包含。 -/
lemma remainingPositionMap_nonpivot_mem_active (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k)
    (r : Fin (m + 1 + d)) (hr : r ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀) :
    a.remainingPositionMap r ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      a.compositePosition := by
  have hrk := a.remaining_color_ne_of_nonpivot q ha hp r hr
  have hr' := (Finset.mem_erase.mp hr).2
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_activePositions_iff_output_and_le _ _ (a.compositePosition_nondegenerate hn) _).2
  constructor
  · rw [a.remainingPositionMap_of_ne r hrk, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition,
      a.compositePosition_remaining_output hn]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u a.val.1 a.property.1 _).2 ⟨r, hr', rfl⟩
  · rw [← a.remainingPositionMap_at_nonpivot_cut hp]
    rcases lt_or_eq_of_le (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot a.property.1 hr') with h | rfl
    · exact ((a.remainingPositionMap_lt_iff r a.val.1 hrk hp).2 h).le
    · exact le_rfl

/-- 概要：外側残り活動像と内側活動像は非交差（BF §2.2.6）。
方針：各残り位置が最初の指定出現の前か後かに分け、厳密順序を使う。
規約：内側 arity の正性は不要。
使われ方：全活動集合の和と逆転数の分解。 -/
lemma nonpivot_active_images_disjoint (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (q : Fin (n + e))
    (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    Disjoint (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀).image a.remainingPositionMap)
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q).image (a.nonpivotInnerMap q ha hp)) := by
  have H := a.property.2
  rw [ha] at H
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hx'
  have hrk := a.remaining_color_ne_of_nonpivot q ha hp r hr
  have hjq := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot H.2 hj
  rcases lt_or_gt_of_ne (Finset.mem_erase.mp hr).1 with h | h
  · exact (ne_of_lt (a.remainingPositionMap_lt_nonpivotInnerMap q ha hp r hrk h j hjq)) he.symm
  · exact (ne_of_lt (a.nonpivotInnerMap_lt_remainingPositionMap q ha hp r hrk h j hjq)) he

/-- 概要：全合成活動集合は外側残り活動像と内側活動像の和（BF §2.2.6）。
方針：非交差な二つの単射像の活動性と全個数 d+e+1 を合わせる。
規約：二出現色分岐の正の内側 arity。
使われ方：合成逆転数を両向き交差公式へ移す。 -/
lemma activePositions_nonpivot_union (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (q : Fin (n + e)) (ha : a.val.2 = some q) (hp : u.val a.val.1 ≠ k) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase r₀).image a.remainingPositionMap ∪
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q).image (a.nonpivotInnerMap q ha hp) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition := by
  have H := a.property.2
  rw [ha] at H
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
      exact a.remainingPositionMap_nonpivot_mem_active hn q ha hp r hr
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
      exact a.nonpivotInnerMap_mem_active hn q ha hp r hr
  · rw [Finset.card_union_of_disjoint (a.nonpivot_active_images_disjoint q ha hp),
      Finset.card_image_of_injOn (a.remainingPositionMap_nonpivot_injOn q ha hp),
      Finset.card_image_of_injOn (a.nonpivotInnerMap_injOn q ha hp),
      Finset.card_erase_of_mem (a.nonpivot_first_mem_active q ha hp),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card u a.val.1 a.property.1, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card v q H.2,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card _ _ (a.compositePosition_nondegenerate hn)]
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
