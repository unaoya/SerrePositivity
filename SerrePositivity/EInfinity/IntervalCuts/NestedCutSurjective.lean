module

public import SerrePositivity.EInfinity.IntervalCuts.InnerCutRecovery
public import SerrePositivity.EInfinity.IntervalCuts.InsertedPivotRecovery

/-!
# 二段切断と非零合成切断の有限同値

概要：Berger–Fresse §2.2.6 の二段切断と非零合成切断が全単射で対応する。
方針：切断点の残り・挿入ラベルを分け、外側非零性と内側の頂点・辺条件を復元する。
規約：正の内側 arity。零 arity の有限和の比較は別工程。
使われ方：部分合成則の両辺の非零項の有限和を添字変更する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：残りラベルの非零合成切断は二段切断からの写像の像に入る（BF §2.2.6）。
方針：一意な外側位置を復元し、指定色一出現では頂点入力、二出現では共有位置の辺入力を使う。
規約：元の分割と実際の合成位置を保持する。
使われ方：有限対応の全射性の残りラベル分岐。 -/
lemma exists_preimage_of_remaining_pivot {m n d e : ℕ}
    (u : BasisWord (m + 1) d) (v : BasisWord n e) (k : Fin (m + 1)) (hn : 0 < n)
    (c : CompositeEdgeCut u v k hn) (b : {b : Fin (m + 1) // b ≠ k})
    (hb : (compositeBasisWord u v k c.val.1 hn).val c.val.2 =
      BarrattEccles.remainingPosition m n k b) :
    ∃ a : NestedEdgeCut u v k, a.toCompositeCut hn = c := by
  obtain ⟨p, ⟨hpb, hp, hq⟩, _⟩ :=
    exists_unique_outer_pivot u v k c.val.1 hn c.val.2 c.property b hb
  have H := c.property
  rw [hq] at H
  have hu := outer_cut_nondegenerate_of_compositeOuterPosition u v k c.val.1 hn p hp H
  have finish (a : NestedEdgeCut u v k) (ha : a.val.1 = p) (hr : a.partition = c.val.1) :
      a.toCompositeCut hn = c := by
    apply Subtype.ext
    refine Prod.ext hr ?_
    change a.compositePosition = c.val.2
    apply pivot_unique c.property
    have hval := NestedEdgeCut.compositePosition_nonpivot_value a hn
      (show u.val a.val.1 ≠ k by rwa [ha])
    rw [hr] at hval
    rw [hval, hb]
    apply congrArg (BarrattEccles.remainingPosition m n k)
    exact Subtype.ext (by simpa only [ha] using hpb)
  by_cases hc : occurrenceCount u.val k = 1
  · have he := inner_degree_zero_of_single_slot_outer_cut u v k c.val.1 hn hc p hp H
    have hk : edgeOutput u p k ≠ edge :=
      (edgeOutput_ne_edge_iff_single_nonpivot u p hu k).mpr ⟨Ne.symm hp, hc⟩
    let a : NestedEdgeCut u v k := NestedEdgeCut.ofVertex p hu hk he
    have hs : Subsingleton (OverlapPartition (occurrenceCount u.val k) (n + e)) := by
      rw [hc]
      exact ⟨fun r t => r.eq_single.trans t.eq_single.symm⟩
    exact ⟨a, finish a rfl (hs.elim _ _)⟩
  · have hle := slot_occurrenceCount_le_two_of_composite_cut u v k c.val.1 hn c.val.2 c.property
    have hpos := occurrenceCount_pos u k
    have hc2 : occurrenceCount u.val k = 2 := by omega
    let r := cast (congrArg (fun t => OverlapPartition t (n + e)) hc2) c.val.1
    let s := OverlapPartition.twoCut (show 0 < n + e by omega) r
    have hv := inner_two_cut_nondegenerate_of_composite u v k c.val.1 hn hc2
      c.val.2 c.property
    have hk := edgeOutput_eq_edge_of_two_occurrences u p hu k hc2
    let a : NestedEdgeCut u v k := NestedEdgeCut.ofEdge p hu hk s hv
    have hr : a.partition = c.val.1 := by
      apply (cast_inj (congrArg (fun t => OverlapPartition t (n + e)) hc2)).mp
      rw [NestedEdgeCut.partition_of_some_nonpivot a s rfl (Ne.symm hp)]
      exact OverlapPartition.two_twoCut (show 0 < n + e by omega) r
    exact ⟨a, finish a rfl hr⟩

namespace NestedEdgeCut

/-- 概要：二段切断から実際の非零合成切断への写像は全射（BF §2.2.6）。
方針：合成切断点ラベルを残り・挿入に分け、それぞれの逆復元を適用する。
規約：正の内側 arity、全外側・内側次数。
使われ方：既存の単射性と合わせて有限同値を構成する。 -/
lemma toCompositeCut_surjective {m n d e : ℕ} {u : BasisWord (m + 1) d}
    {v : BasisWord n e} {k : Fin (m + 1)} (hn : 0 < n) :
    Function.Surjective (toCompositeCut (u := u) (v := v) (k := k) hn) := by
  intro c
  let x := (compositeBasisWord u v k c.val.1 hn).val c.val.2
  cases hx : operadInsertionEquiv m n k x with
  | inl b =>
    apply exists_preimage_of_remaining_pivot u v k hn c b
    have H := congrArg (operadInsertionEquiv m n k).symm hx
    simpa only [Equiv.symm_apply_apply, BarrattEccles.remainingPosition] using H
  | inr b =>
    apply exists_preimage_of_inserted_pivot u v k hn c b
    have H := congrArg (operadInsertionEquiv m n k).symm hx
    simpa only [Equiv.symm_apply_apply, BarrattEccles.insertedPosition] using H

/-- 概要：二段切断と非零合成切断の有限同値（BF §2.2.6）。
方針：実際の位置構成の単射性・全射性を束ねる。
規約：順方向は既存の toCompositeCut そのもの。
使われ方：合成則の非零項の有限和の添字変更。 -/
noncomputable def compositeCutEquiv {m n d e : ℕ} {u : BasisWord (m + 1) d}
    {v : BasisWord n e} {k : Fin (m + 1)} (hn : 0 < n) :
    NestedEdgeCut u v k ≃ CompositeEdgeCut u v k hn :=
  Equiv.ofBijective (toCompositeCut hn)
    ⟨toCompositeCut_injective hn, toCompositeCut_surjective hn⟩

end NestedEdgeCut

end SerrePositivity.EInfinity.IntervalCuts
