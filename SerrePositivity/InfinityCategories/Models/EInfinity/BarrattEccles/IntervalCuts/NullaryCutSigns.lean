module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NullaryCutEquiv
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionReindex

/-!
模型。文献の定義との比較は後で
# 空語合成の活動位置と切断符号

概要：Berger–Fresse §2.2.4・§2.2.6 の nullary の切断符号保存を証明する。
方針：指定色以外の活動位置の像を全活動集合へ同定し、位置と色の順序を比較する。
規約：削除語全体の非退化性は要求せず、非零切断ごとに基底語を得る。
使われ方：空語合成の実際の左右のテンソル和の整数係数一致。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

namespace NestedEdgeCut

variable {m d : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0} {k : Fin (m + 1)}

/-- 概要：空語代入の外側全位置上の残り位置写像（BF §2.2.6）。
方針：残り色では実際の合成位置、指定色では合成切断点を返す。
規約：指定色での値は活動集合上では使わない。
使われ方：全活動集合の有限像を定義する。 -/
def nullaryPositionMap (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) (q : Fin (m + 1 + d)) : Fin (m + d) :=
  if hq : u.val q ≠ k then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r q hq
  else _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r a.val.1 a.nullary_pivot_ne_slot

/-- 概要：空語代入の活動位置像は削除語の全活動集合（BF §2.2.4・§2.2.6）。
方針：残り出力の辺条件と位置順序で包含を示し、両者の d+1 個を比較する。
規約：固定した空語分割と実際の二段切断を使う。
使われ方：切断符号の全逆転数を元の活動集合へ戻す。 -/
lemma nullaryPositionMap_image (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).image (a.nullaryPositionMap r) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a).val := by
  have hne (q : Fin (m + 1 + d)) (hq : q ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) : u.val q ≠ k :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k a.nullary_slot_nonedge q hq
  have hmono (q s : Fin (m + 1 + d)) (hq : u.val q ≠ k) (hs : u.val s ≠ k) :
      a.nullaryPositionMap r q < a.nullaryPositionMap r s ↔ q < s := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.nullaryPositionMap, dite_eq_left hq, dite_eq_left hs]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt_iff u v k r q s hq hs
  have hinj : Set.InjOn (a.nullaryPositionMap r) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) := by
    intro q hq s hs he
    rcases lt_trichotomy q s with h | h | h
    · exact False.elim ((ne_of_lt ((hmono q s (hne q hq) (hne s hs)).mpr h)) he)
    · exact h
    · exact False.elim ((ne_of_lt ((hmono s q (hne s hs) (hne q hq)).mpr h)) he.symm)
  let w := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawCutWord u v k r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a)
  have hw := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a).property
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.mem_activePositions_iff_output_and_le w _ hw _).mpr
    constructor
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.nullaryPositionMap, dite_eq_left (hne q hq)]
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput w _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r q (hne q hq))) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_outerPosition]
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawCutWord u v k r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a).val _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv_remaining_output]
      exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_eq_edge_iff u a.val.1 a.property.1 _).mpr ⟨q, hq, rfl⟩
    · have he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a).val =
          a.nullaryPositionMap r a.val.1 := by
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.nullaryPositionMap, dite_eq_left a.nullary_pivot_ne_slot]
        rfl
      rw [he]
      rcases lt_or_eq_of_le (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_le_pivot a.property.1 hq) with h | rfl
      · exact ((hmono q a.val.1 (hne q hq) a.nullary_pivot_ne_slot).mpr h).le
      · exact le_rfl
  · rw [Finset.card_image_of_injOn hinj]
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions w.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a).val).card ≤ _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card w _ hw, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card u _ a.property.1]

/-- 概要：空語合成の各逆転対は外側活動位置の同じ逆転対（BF §2.2.4）。
方針：残り位置と残り色の厳密順序をともに元へ戻す。
規約：指定色は活動集合に現れない。
使われ方：二重和の各項を同定して全逆転数を保存する。 -/
lemma nullaryPositionMap_inversionTerm (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) (q s : Fin (m + 1 + d))
    (hq : q ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) (hs : s ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r)
      (a.nullaryPositionMap r q) (a.nullaryPositionMap r s) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val q s := by
  have hqk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k
    a.nullary_slot_nonedge q hq
  have hsk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k
    a.nullary_slot_nonedge s hs
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.nullaryPositionMap, dite_eq_left hqk, dite_eq_left hsk]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_outerPosition,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt_iff u v k r q s hqk hsk]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remainingPosition_lt_iff k
    (⟨u.val s, hsk⟩ : {j : Fin (m + 1) // j ≠ k}) ⟨u.val q, hqk⟩]

/-- 概要：空語合成の切断符号は外側の切断符号（BF §2.2.4・§2.2.6）。
方針：全活動集合を単射像へ移し、各位置対の逆転寄与を保つ。
規約：全外側語次数と任意の空語分割。
使われ方：実際の nullary 合成項と二段作用の一般係数の比較。 -/
lemma nullary_edgeSign (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a).val =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign u.val a.val.1 := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryNestedCutEquiv u v k r a).property,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeSign_eq_inversionCount a.property.1, ← a.nullaryPositionMap_image r]
  congr 1
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_image_of_terms
  · intro q hq s hs he
    have hqk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k
      a.nullary_slot_nonedge q hq
    have hsk := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePosition_color_ne_of_nonedge u a.val.1 a.property.1 k
      a.nullary_slot_nonedge s hs
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut.nullaryPositionMap, dite_eq_left hqk, dite_eq_left hsk] at he
    rcases lt_trichotomy q s with h | h | h
    · exact False.elim ((ne_of_lt (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt u v k r q s hqk hsk h)) he)
    · exact h
    · exact False.elim ((ne_of_lt (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition_lt u v k r s q hsk hqk h)) he.symm)
  · exact fun q hq s hs => a.nullaryPositionMap_inversionTerm r q s hq hs

end NestedEdgeCut

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
