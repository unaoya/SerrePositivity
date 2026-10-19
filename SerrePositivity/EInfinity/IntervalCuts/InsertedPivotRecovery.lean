module

public import SerrePositivity.EInfinity.IntervalCuts.SegmentBoundaryCuts
public import SerrePositivity.EInfinity.IntervalCuts.SingleSlotCutRecovery
public import SerrePositivity.EInfinity.IntervalCuts.NestedCutInjective

/-!
# 挿入ラベルを切断点とする非零合成切断の復元

概要：Berger–Fresse §2.2.6 の挿入ラベル切断点は一出現挿入に限られる。
方針：元の内側位置を覆う部分語へ切断点を戻し、共有端点を跨ぐ条件と比較する。
規約：正の内側 arity、任意の外側・内側次数。
使われ方：二段切断の逆対応の切断点色分岐を一出現性の追加仮定なしで構成する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：挿入ラベルの非零合成切断点はいずれかの部分語内の位置（BF §2.2.6）。
方針：元の内側位置を覆う部分語を取り、合成切断点色の一意性で位置を照合する。
規約：外側指定色の出現数を制限しない。
使われ方：共有端点の間にある切断点が挿入部分語内にあることの矛盾。 -/
lemma exists_segmentPosition_of_inserted_pivot {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q) (b : Fin n)
    (hb : (compositeBasisWord u v k r hn).val q =
      BarrattEccles.insertedPosition m n k b) :
    ∃ i : Fin (occurrenceCount u.val k), ∃ a : Fin (r.val i).val,
      q = compositeSegmentPosition u v k r i a := by
  obtain ⟨s, hs⟩ := v.surjective b
  obtain ⟨i, hlo, hhi⟩ := r.position_covered (occurrenceCount_pos u k) s
  let a : Fin (r.val i).val := ⟨s.val - r.start i, by omega⟩
  refine ⟨i, a, ?_⟩
  apply Eq.symm
  apply pivot_unique h
  rw [compositeSegmentPosition_value]
  have he : (⟨r.start i + a.val, by
      have := r.start_add_length_le i; have := a.isLt; omega⟩ : Fin (n + e)) = s := by
    apply Fin.ext
    change r.start i + (s.val - r.start i) = s.val
    omega
  rw [he, hs, hb]

/-- 概要：挿入ラベルが非零合成切断点なら外側指定色は一出現（BF §2.2.6）。
方針：出現数上限は二で、二部分割なら共有端点の間に切断点があり両部分語の内部から外れる。
規約：外側の非零性も一出現性も仮定しない。
使われ方：切断点色分岐を既存の一出現挿入の逆復元へ帰着する。 -/
lemma slot_occurrenceCount_eq_one_of_inserted_pivot {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q) (b : Fin n)
    (hb : (compositeBasisWord u v k r hn).val q =
      BarrattEccles.insertedPosition m n k b) : occurrenceCount u.val k = 1 := by
  have hle := slot_occurrenceCount_le_two_of_composite_cut u v k r hn q h
  have hpos := occurrenceCount_pos u k
  by_contra hc
  have hc2 : occurrenceCount u.val k = 2 := by omega
  let i : Fin (occurrenceCount u.val k) := ⟨0, by omega⟩
  let j : Fin (occurrenceCount u.val k) := ⟨1, by omega⟩
  have H := compositeSegment_boundary_straddles u v k r hn q h i j rfl
  obtain ⟨s, a, hs⟩ := exists_segmentPosition_of_inserted_pivot u v k r hn q h b hb
  have hslt := s.isLt
  by_cases hs0 : s.val = 0
  · have he : s = i := Fin.ext hs0
    subst s
    have ha : compositeSegmentPosition u v k r i a ≤ compositeSegmentLast u v k r hn i := by
      change _ + a.val ≤ _ + ((r.val i).val - 1)
      have := a.isLt
      omega
    rw [← hs] at ha
    exact (not_lt_of_ge ha) H.1
  · have he : s = j := Fin.ext (by change s.val = 1; omega)
    subst s
    have ha : compositeSegmentFirst u v k r hn j ≤ compositeSegmentPosition u v k r j a := by
      change _ + 0 ≤ _ + a.val
      omega
    rw [← hs] at ha
    exact (not_lt_of_ge ha) H.2

/-- 概要：挿入ラベルの非零合成切断点から一出現性と両非零切断を復元（BF §2.2.6）。
方針：共有端点の制約で一出現性を導き、同じ合成位置の一出現逆復元を適用する。
規約：分割と切断点の実際の位置を保持する。
使われ方：有限全単射の逆方向の切断点色分岐。 -/
lemma exists_cuts_of_inserted_pivot {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) (n + e)) (hn : 0 < n)
    (q : Fin (m + n + (d + e)))
    (h : EdgeNondegenerate (compositeBasisWord u v k r hn).val q) (b : Fin n)
    (hb : (compositeBasisWord u v k r hn).val q =
      BarrattEccles.insertedPosition m n k b) :
    ∃ hc : occurrenceCount u.val k = 1, ∃ p : Fin (m + 1 + d), ∃ hp : u.val p = k,
      ∃ s : Fin (n + e), v.val s = b ∧ EdgeNondegenerate u.val p ∧
        EdgeNondegenerate v.val s ∧ q = compositeInnerPosition u v k r hc p hp s := by
  have hc := slot_occurrenceCount_eq_one_of_inserted_pivot u v k r hn q h b hb
  exact ⟨hc, exists_single_slot_cuts_of_inserted_pivot u v k r hc hn q h b hb⟩

/-- 概要：挿入ラベルの非零合成切断は二段切断からの写像の像に入る（BF §2.2.6）。
方針：復元した両非零切断で二段切断を作り、一部分割の一意性と同じ合成位置を照合する。
規約：元の実際の分割・切断点を持つ有限添字への等式として述べる。
使われ方：全射性の挿入ラベル分岐。 -/
lemma exists_preimage_of_inserted_pivot {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1)) (hn : 0 < n)
    (c : CompositeEdgeCut u v k hn) (b : Fin n)
    (hb : (compositeBasisWord u v k c.val.1 hn).val c.val.2 =
      BarrattEccles.insertedPosition m n k b) :
    ∃ a : NestedEdgeCut u v k, a.toCompositeCut hn = c := by
  obtain ⟨hc, p, hp, s, _, hu, hv, he⟩ :=
    exists_cuts_of_inserted_pivot u v k c.val.1 hn c.val.2 c.property b hb
  have hedge : edgeOutput u p k = edge :=
    (edgeOutput_eq_edge_iff u p hu k).mpr ⟨p, Finset.mem_insert_self _ _, hp⟩
  let a : NestedEdgeCut u v k := NestedEdgeCut.ofEdge p hu hedge s hv
  have hs : Subsingleton (OverlapPartition (occurrenceCount u.val k) (n + e)) := by
    rw [hc]
    exact ⟨fun r t => r.eq_single.trans t.eq_single.symm⟩
  have hr : a.partition = c.val.1 := hs.elim _ _
  refine ⟨a, Subtype.ext (Prod.ext hr ?_)⟩
  change a.compositePosition = c.val.2
  apply Fin.ext
  rw [NestedEdgeCut.compositePosition_pivot_val a s rfl hp, hr]
  simpa only [a, NestedEdgeCut.ofEdge, compositeInnerPosition] using congrArg Fin.val he.symm

end SerrePositivity.EInfinity.IntervalCuts
