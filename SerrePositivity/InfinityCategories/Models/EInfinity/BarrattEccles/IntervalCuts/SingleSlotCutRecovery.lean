module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonSlotCutRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SingleSlotCut
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NestedCutPositions

/-!
模型。文献の定義との比較は後で
# 一出現挿入の内側切断からの非零性の復元

概要：Berger–Fresse §2.2.6 の一出現挿入で、合成の非零性から外側・内側の非零性を戻す。
方針：実際の合成語の左右を三ブロックの take・drop に分け、各 Nodup を取り出す。
規約：切断点は挿入部分語の中にあり、指定色は外側語で一出現。
使われ方：二段切断の切断点色分岐の逆対応。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：内側位置の非零合成切断から外側・内側の非零切断を回収（BF §2.2.6）。
方針：合成の左右 Nodup から前後と内側の左右を分離し、残り色の count を戻す。
規約：正の内側 arity、指定色の一出現、実際の合成基底語。
使われ方：順方向の一出現挿入の非退化性と合わせた必要十分条件。 -/
lemma single_slot_cuts_nondegenerate_of_composite {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p = k)
    (q : Fin (n + e)) (hn : 0 < n)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q := by
  have hL := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_prefix_nodup _ _ h
  have hR := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_suffix_nodup _ _ h
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord_list, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeWord_at_single_slot u v k r hc p hp,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition] at hL hR
  rw [Nat.add_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.splice_take_inside _ _ _ _ (by
    simp only [List.length_map, List.length_ofFn]; omega)] at hL
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.splice_drop_inside _ _ _ _ (by
    simp only [List.length_map, List.length_ofFn]; omega)] at hR
  have hpre := (List.nodup_append.mp hL).1
  have hpost := (List.nodup_append.mp hR).2.1
  have hmidL := (List.nodup_append.mp hL).2.1
  have hmidR := (List.nodup_append.mp hR).1
  have hpreNot := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_not_mem_prefix u.val k hc p hp
  have hpostNot := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_not_mem_suffix u.val k hc p hp
  have hpreN := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nodup_of_substitute_nodup k _ _ hpre
    (by simp only [List.count_eq_zero.mpr hpreNot]; omega)
  have hpostN := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nodup_of_substitute_nodup k _ _ hpost
    (by simp only [List.count_eq_zero.mpr hpostNot]; omega)
  constructor
  · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_nondegenerate_of_nodup
    · have hl : p.val < (List.ofFn u.val).length := by
        simpa only [List.length_ofFn] using p.isLt
      rw [List.take_succ_eq_append_getElem hl, List.getElem_ofFn, hp]
      simpa only [List.concat_eq_append] using List.Nodup.concat hpreNot hpreN
    · have hl : p.val < (List.ofFn u.val).length := by
        simpa only [List.length_ofFn] using p.isLt
      rw [List.drop_eq_getElem_cons hl, List.getElem_ofFn, hp, List.nodup_cons]
      exact ⟨hpostNot, hpostN⟩
  · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cut_nondegenerate_of_nodup
    · rw [← List.map_take] at hmidL
      exact List.Nodup.of_map _ hmidL
    · rw [← List.map_drop] at hmidR
      exact List.Nodup.of_map _ hmidR

/-- 概要：一出現挿入の内側切断の非零性は外側・内側の非零性と同値（BF §2.2.6）。
方針：三ブロックの逆復元と既存の順方向の非零性を組み合わせる。
規約：同じ分割・指定位置・実際の合成基底語を両方向で保つ。
使われ方：有限全単射の切断点色分岐の非退化性の照合。 -/
lemma composite_single_slot_cut_nondegenerate_iff {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (p : Fin (m + 1 + d)) (hp : u.val p = k)
    (q : Fin (n + e)) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q) ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q := by
  constructor
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_cuts_nondegenerate_of_composite u v k r hc p hp q hn
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.composite_single_slot_cut_nondegenerate u v k r hc p hp h.1 q h.2 hn

/-- 概要：一出現挿入の挿入ラベル切断点から二つの非零切断を復元（BF §2.2.6）。
方針：両基底語の全射性で同色位置を取り、合成切断点の一意性から実際の位置を照合する。
規約：一出現性を入力として明示し、任意の内側次数を許す。
使われ方：一般の逆対応で一出現性を示した後の切断点色分岐を閉じる。 -/
lemma exists_single_slot_cuts_of_inserted_pivot {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e))
    (hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k = 1) (hn : 0 < n)
    (s : Fin (m + n + (d + e)))
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val s) (b : Fin n)
    (hb : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeBasisWord u v k r hn).val s =
      _root_.SerrePositivity.EInfinity.BarrattEccles.insertedPosition m n k b) :
    ∃ p : Fin (m + 1 + d), ∃ hp : u.val p = k, ∃ q : Fin (n + e),
      v.val q = b ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u.val p ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate v.val q ∧
        s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q := by
  obtain ⟨p, hp⟩ := u.surjective k
  obtain ⟨q, hq⟩ := v.surjective b
  have he : s = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeInnerPosition u v k r hc p hp q := by
    apply Eq.symm
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique hs
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeBasisWord_innerPosition u v k r hc p hp q hn, hq, hb]
  have H := hs
  rw [he] at H
  have hcuts := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.single_slot_cuts_nondegenerate_of_composite u v k r hc p hp q hn H
  exact ⟨p, hp, q, hq, hcuts.1, hcuts.2, he⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
