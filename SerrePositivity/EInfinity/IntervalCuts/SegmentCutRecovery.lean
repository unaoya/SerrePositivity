module

public import SerrePositivity.EInfinity.IntervalCuts.OuterCutRecovery

/-!
# 合成切断の片側に収まる挿入部分語の非退化性

概要：Berger–Fresse §2.2.6 の非零合成切断の片側にある挿入部分語は Nodup。
方針：実際の部分語位置を合成語へ送り、切断の片側単射性を戻す。
規約：左右のいずれも切断点を含めてよい。
使われ方：逆対応で一部分割の次数零と二部分割の内側非零性を復元する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：非零合成切断の同じ側にある挿入部分語は重複を持たない（BF §2.2.6）。
方針：リスト位置の同色性を合成位置へ送り、左右単射性と位置の平行移動の単射性を使う。
規約：片側条件は全内部位置に対して述べる。
使われ方：共有端点の前後にある部分語の Nodup。 -/
lemma segment_nodup_of_same_side {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (i : Fin (occurrenceCount u.val k))
    (hside : (∀ a, compositeSegmentPosition u v k r i a ≤ q) ∨
      (∀ a, q ≤ compositeSegmentPosition u v k r i a)) : (r.segment v.val i).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro a b hab
  let a' : Fin (r.val i).val :=
    ⟨a.val, by simpa only [OverlapPartition.segment_length] using a.isLt⟩
  let b' : Fin (r.val i).val :=
    ⟨b.val, by simpa only [OverlapPartition.segment_length] using b.isLt⟩
  have hc : (compositeBasisWord u v k r hn).val (compositeSegmentPosition u v k r i a') =
      (compositeBasisWord u v k r hn).val (compositeSegmentPosition u v k r i b') := by
    rw [compositeSegmentPosition_value, compositeSegmentPosition_value]
    apply congrArg (BarrattEccles.insertedPosition m n k)
    simpa only [OverlapPartition.segment, List.getElem_take, List.getElem_drop,
      List.getElem_ofFn] using hab
  have he : compositeSegmentPosition u v k r i a' =
      compositeSegmentPosition u v k r i b' := by
    rcases hside with hL | hR
    · exact edge_left_injective h _ _ (hL a') (hL b') hc
    · exact edge_right_injective h _ _ (hR a') (hR b') hc
  apply Fin.ext
  have hv := congrArg Fin.val he
  exact Nat.add_left_cancel hv

/-- 概要：挿入部分語の末尾が非零切断点以前ならその部分語は Nodup（BF §2.2.6）。
方針：全内部位置を末尾以下で抑えて左側単射性を使う。
規約：末尾と切断点の一致も許す。
使われ方：二部分割の前半の内側非退化性。 -/
lemma segment_nodup_of_last_le_cut {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (i : Fin (occurrenceCount u.val k)) (hi : compositeSegmentLast u v k r hn i ≤ q) :
    (r.segment v.val i).Nodup := by
  apply segment_nodup_of_same_side u v k r hn q h i
  left
  intro a
  apply le_trans ?_ hi
  change _ + a.val ≤ _ + ((r.val i).val - 1)
  have := a.isLt
  omega

/-- 概要：非零切断点が挿入部分語の先頭以前ならその部分語は Nodup（BF §2.2.6）。
方針：全内部位置を先頭以上で抑えて右側単射性を使う。
規約：先頭と切断点の一致も許す。
使われ方：二部分割の後半の内側非退化性。 -/
lemma segment_nodup_of_cut_le_first {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q)
    (i : Fin (occurrenceCount u.val k)) (hi : q ≤ compositeSegmentFirst u v k r hn i) :
    (r.segment v.val i).Nodup := by
  apply segment_nodup_of_same_side u v k r hn q h i
  right
  intro a
  apply le_trans hi
  change _ + 0 ≤ _ + a.val
  omega

end SerrePositivity.EInfinity.IntervalCuts
