module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotActivePositions
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InversionBlocks

/-!
模型。文献の定義との比較は後で
# 切断点色への挿入の合成逆転数

概要：Berger–Fresse §2.2.6 の合成切断の全逆転数を内外と一様交差項で評価する。
方針：前後二つの活動像の内部寄与と交差寄与を元の位置と色へ戻す。
規約：内側語次数は任意で、正の内側 arity。
使われ方：切断点色分岐の一般符号等式。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable {m n d e : ℕ} {u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d} {v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e} {k : Fin (m + 1)}

/-- 概要：任意の残り二位置の逆転寄与は合成前後で一致（BF §2.2.4・§2.2.6）。
方針：残り位置と残り色の厳密順序を同時に戻す。
規約：活動性や非辺入力を仮定しない。
使われ方：内側辺作用の外側残り活動ブロックの内部逆転数。 -/
lemma remainingPositionMap_inversionTerm_of_ne (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (r s : Fin (m + 1 + d)) (hr : u.val r ≠ k) (hs : u.val s ≠ k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      (a.remainingPositionMap r) (a.remainingPositionMap s) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm u.val r s := by
  have hvr : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val (a.remainingPositionMap r) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u.val r, hr⟩ := by
    rw [a.remainingPositionMap_of_ne r hr, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition]
  have hvs : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val (a.remainingPositionMap s) =
      _root_.SerrePositivity.EInfinity.BarrattEccles.remainingPosition m n k ⟨u.val s, hs⟩ := by
    rw [a.remainingPositionMap_of_ne s hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, hvr, hvs, a.remainingPositionMap_lt_iff r s hr hs,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.remainingPosition_lt_iff]

/-- 概要：内側二位置の逆転寄与は挿入後も一致（BF §2.2.4・§2.2.6）。
方針：内側位置は共通の前置長、色は共通の番号だけずれることを使う。
規約：全内側位置で成立する。
使われ方：内側活動ブロックの内部逆転数。 -/
lemma pivotInnerMap_inversionTerm (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hp : u.val a.val.1 = k) (r s : Fin (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      (a.pivotInnerMap hp r) (a.pivotInnerMap hp s) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm v.val r s := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionTerm, a.pivotInnerMap_value hn hp,
    a.pivotInnerMap_lt_iff hp r s, Fin.lt_def, _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition_val,
    Nat.add_lt_add_iff_left]

/-- 概要：切断点色への挿入の全逆転数は内外逆転数と活動数倍の交差数（BF §2.2.6）。
方針：合成活動集合を二つの像へ分け、内部と一様な交差の逆転数を計算する。
規約：外側切断点自身は外側の活動集合から除く。
使われ方：実際の切断符号を二段作用の二交換符号へ比較する。 -/
lemma inversionCount_pivot (a : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut u v k) (hn : 0 < n)
    (hp : u.val a.val.1 = k) (q : Fin (n + e)) (ha : a.val.2 = some q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val a.compositePosition) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount u.val ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1) +
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q) +
            (e + 1) * (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1).filter
              (fun r => k < u.val r)).card := by
  have Hq := a.property.2
  rw [ha] at Hq
  rw [← a.activePositions_pivot_union hn hp q ha]
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.positionInversionCount_ordered_images u.val v.val
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k a.partition hn).val
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions u.val a.val.1).erase a.val.1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions v.val q)
    a.remainingPositionMap (a.pivotInnerMap hp) (a.remainingPositionMap_pivot_injOn hp)
    (fun _ _ _ _ he => a.pivotInnerMap_injective hp he)
    (fun r hr j _ => a.remainingPositionMap_pivot_order hp r hr j)
    (fun r hr s hs => a.remainingPositionMap_inversionTerm_of_ne hn r s
      (a.remaining_color_ne_of_pivot hp r (Finset.mem_erase.mp hr).1)
      (a.remaining_color_ne_of_pivot hp s (Finset.mem_erase.mp hs).1))
    (fun r _ s _ => a.pivotInnerMap_inversionTerm hn hp r s) (fun r => k < u.val r)
    (by
      intro r hr j _
      have hrk := a.remaining_color_ne_of_pivot hp r (Finset.mem_erase.mp hr).1
      rw [a.pivotInnerMap_value hn hp, a.remainingPositionMap_of_ne r hrk,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_outerPosition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.insertedPosition_lt_remaining_iff])
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.activePositions_card v q Hq.2] using H

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedEdgeCut
