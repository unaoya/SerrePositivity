module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotLists
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ListCutSplice

/-!
模型。文献の定義との比較は後で
# 切断点色への一出現挿入の非退化性

概要：Berger–Fresse §2.2.6 の外側切断点色に内側の辺切断を挿入し、実際の合成切断を構成する。
方針：指定色のない前後のラベル像と内側切断の左右リストを非交差に連結する。
規約：一出現の指定色、正の内側 arity と任意の内外語次数。
使われ方：二段切断から合成語の非零切断への順方向写像の切断点色分岐。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：切断点色への一出現挿入は内側の非零切断を合成語の非零切断へ送る（BF §2.2.6）。
方針：外側前後の重複消滅、内側の左右重複消滅、内外ラベルの非交差を使う。
規約：出力は既存の実際の合成基底語と有限位置。
使われ方：二段切断と合成切断の有限対応の順方向の非退化性。 -/
lemma composite_single_slot_cut_nondegenerate {m n d e : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1)
    (p : Fin (m + 1 + d)) (hp : u.val p = k) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p)
    (q : Fin (n + e)) (hq : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q) := by
  have hpreNot := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_not_mem_prefix u.val k hc p hp
  have hpostNot := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_not_mem_suffix u.val k hc p hp
  have hpreN : ((List.ofFn u.val).take p.val).Nodup := by
    have H : (((List.ofFn u.val).take (p.val + 1)).take p.val).Nodup :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_prefix_nodup u.val p h).take
    simpa only [List.take_take, Nat.min_eq_left (Nat.le_succ p.val)] using H
  have hpostN : ((List.ofFn u.val).drop (p.val + 1)).Nodup := by
    have H := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_suffix_nodup u.val p h).tail
    simpa only [List.tail_drop] using H
  have hins := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.insertedPosition_injective m n k
  have hmidL := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_prefix_nodup v.val q hq).map hins
  have hmidR := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_suffix_nodup v.val q hq).map hins
  rw [List.map_take] at hmidL
  rw [List.map_drop] at hmidR
  have hpre := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_nodup_of_no_slot k (v.val q)
    ((List.ofFn u.val).take p.val) (r.segments v.val) hpreNot hpreN
  have hpost := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_nodup_of_no_slot k (v.val q)
    ((List.ofFn u.val).drop (p.val + 1)) [] hpostNot hpostN
  have hdL := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_disjoint_inserted k (v.val q)
    ((List.ofFn u.val).take p.val) (r.segments v.val) (List.ofFn v.val) hpreNot
  have hdR := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.substitute_disjoint_inserted k (v.val q)
    ((List.ofFn u.val).drop (p.val + 1)) [] (List.ofFn v.val) hpostNot
  let q' : Fin ((List.ofFn v.val).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k)).length :=
    ⟨q.val, by simpa only [List.length_map, List.length_ofFn] using q.isLt⟩
  have H := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.splice_cut_nodup
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).take p.val) (r.segments v.val))
    ((List.ofFn v.val).map (_root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.substitute k ((List.ofFn u.val).drop (p.val + 1)) []) q'
    hpre hpost hmidL hmidR hdL hdR.symm
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_nondegenerate_of_nodup
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_single_slot u v k r hc p hp,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition, q'] using H.1
  · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_single_slot u v k r hc p hp,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition, q'] using H.2

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
