module

public import SerrePositivity.EInfinity.IntervalCuts.NullaryRawWord
public import SerrePositivity.EInfinity.IntervalCuts.RemainingPositionOrder

/-!
# 空語合成の正規化前の非零切断対応

概要：Berger–Fresse §2.2.6 の nullary 合成の非零切断を外側切断へ戻す。
方針：左右の代入リストの Nodup と、残り色である切断点の一意性を使う。
規約：削除語全体の非退化性を仮定しない。
使われ方：空語合成の辺切断和を実際の二段切断和へ移す有限対応。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.EInfinity.IntervalCuts

open Surjection

/-- 概要：残り位置での空語合成切断の非零性は外側切断と同値（BF §2.2.6）。
方針：左右の代入リストの Nodup を両方向に移し、空語分割から一出現性を得る。
規約：切断点の色は指定色以外、削除語の非退化性は仮定しない。
使われ方：nullary の切断対応の順方向と逆方向。 -/
lemma nullaryRawWord_cut_iff {m d : ℕ} (u : BasisWord (m + 1) d) (v : BasisWord 0 0)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hp : u.val p ≠ k) :
    EdgeNondegenerate (nullaryRawWord u v k r) (compositeOuterPosition u v k r p hp) ↔
      EdgeNondegenerate u.val p := by
  constructor
  · intro h
    apply cut_nondegenerate_of_nodup
    · apply nodup_of_substitute_nodup k _ (r.segments v.val) _
        ((List.Sublist.count_le k (List.take_sublist _ _)).trans
          (Nat.le_of_eq r.count_eq_one_of_empty))
      rw [← nullaryRawWord_prefix u v k r p hp]
      exact cut_prefix_nodup _ _ h
    · apply nodup_of_substitute_nodup k _
        ((r.segments v.val).drop (((List.ofFn u.val).take p.val).count k)) _
        ((List.Sublist.count_le k (List.drop_sublist _ _)).trans
          (Nat.le_of_eq r.count_eq_one_of_empty))
      rw [← nullaryRawWord_suffix u v k r p hp]
      exact cut_suffix_nodup _ _ h
  · intro h
    have hz (part : List (Fin 0)) : part.Nodup := by
      cases part with
      | nil => exact List.nodup_nil
      | cons a _ => exact Fin.elim0 a
    apply cut_nondegenerate_of_nodup
    · rw [nullaryRawWord_prefix]
      exact substitute_nodup_of_parts k _ _ (cut_prefix_nodup u.val p h) (fun part _ => hz part)
    · rw [nullaryRawWord_suffix]
      exact substitute_nodup_of_parts k _ _ (cut_suffix_nodup u.val p h) (fun part _ => hz part)

/-- 概要：空語合成の各非零切断は残り外側位置から来る（BF §2.2.6）。
方針：切断点色を残りラベルへ分解し、外側の全射性と切断点の一意性を使う。
規約：非零性を持つ切断点だけを戻し、退化削除語も許す。
使われ方：nullary の非零切断対応の全射性。 -/
lemma nullaryRawWord_cut_preimage {m d : ℕ} (u : BasisWord (m + 1) d)
    (v : BasisWord 0 0) (k : Fin (m + 1))
    (r : OverlapPartition (occurrenceCount u.val k) 0) (q : Fin (m + d))
    (hq : EdgeNondegenerate (nullaryRawWord u v k r) q) :
    ∃ (p : Fin (m + 1 + d)) (hp : u.val p ≠ k),
      q = compositeOuterPosition u v k r p hp := by
  have hs := (operadInsertionEquiv m 0 k).symm_apply_apply (nullaryRawWord u v k r q)
  cases ha : operadInsertionEquiv m 0 k (nullaryRawWord u v k r q) with
  | inl a =>
    have he : nullaryRawWord u v k r q = BarrattEccles.remainingPosition m 0 k a := by
      simpa only [ha, BarrattEccles.remainingPosition] using hs.symm
    obtain ⟨p, hp⟩ := u.surjective a.val
    have hpk : u.val p ≠ k := fun h => a.property (hp.symm.trans h)
    refine ⟨p, hpk, ?_⟩
    apply (pivot_unique hq _ ?_).symm
    rw [nullaryRawWord_outerPosition]
    exact (congrArg (BarrattEccles.remainingPosition m 0 k) (Subtype.ext hp)).trans he.symm
  | inr a => exact Fin.elim0 a

/-- 概要：空語合成の非零切断と残り外側非零切断の有限同値（BF §2.2.6）。
方針：残り位置写像の厳密順序で単射性、切断点の復元で全射性を示す。
規約：一出現性は空語の合成分割が保持し、退化削除語も含む。
使われ方：nullary の実際の辺成分の有限和の添字替え。 -/
def nullaryRawCutEquiv {m d : ℕ} (u : BasisWord (m + 1) d) (v : BasisWord 0 0)
    (k : Fin (m + 1)) (r : OverlapPartition (occurrenceCount u.val k) 0) :
    {p : Fin (m + 1 + d) // EdgeNondegenerate u.val p ∧ u.val p ≠ k} ≃
      {q : Fin (m + d) // EdgeNondegenerate (nullaryRawWord u v k r) q} :=
  Equiv.ofBijective (fun p => ⟨compositeOuterPosition u v k r p.val p.property.2,
    (nullaryRawWord_cut_iff u v k r p.val p.property.2).mpr p.property.1⟩) (by
    constructor
    · intro p q h
      have he := congrArg Subtype.val h
      apply Subtype.ext
      rcases lt_trichotomy p.val q.val with hlt | heq | hlt
      · exact False.elim ((ne_of_lt
          (compositeOuterPosition_lt u v k r p.val q.val p.property.2 q.property.2 hlt)) he)
      · exact heq
      · exact False.elim ((ne_of_lt
          (compositeOuterPosition_lt u v k r q.val p.val q.property.2 p.property.2 hlt)) he.symm)
    · intro q
      obtain ⟨p, hp, he⟩ := nullaryRawWord_cut_preimage u v k r q.val q.property
      have hc : EdgeNondegenerate u.val p :=
        (nullaryRawWord_cut_iff u v k r p hp).mp (he ▸ q.property)
      exact ⟨⟨p, hc, hp⟩, Subtype.ext he.symm⟩)

end SerrePositivity.EInfinity.IntervalCuts
