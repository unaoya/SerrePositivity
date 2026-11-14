module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeOuterEndpoints
public import SerrePositivity.EInfinity.SimplexCuts.PositiveOccurrencePosition
public import SerrePositivity.EInfinity.IntervalCuts.CompositionCutPositions

/-!
# 同じ合成語に残る外側の位置と文字

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の指定面の照合。
元の指定色以外の文字は、同じ接頭長で一文字のまま読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C451e：元の指定色以外の一文字で接頭長は一だけ増える（BF §2.2.6）。 -/
lemma compositePrefixLength_at_non_slot {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    compositePrefixLength u v k r (p.val + 1) = compositePrefixLength u v k r p.val + 1 := by
  let p' : Fin ((m + 1) + d) := ⟨p.val, by have h := p.isLt; omega⟩
  have hw : (positiveWord u).val p = u.val p' := by
    unfold positiveWord
    exact word_eq_mp_value (by omega : (m + 1) + d = m + d + 1) u p p' rfl
  have hu : u.val p' ≠ k := fun h => hp (hw.trans h)
  let pList : Fin (List.ofFn u.val).length := ⟨p.val, by simp only [List.length_ofFn]; omega⟩
  have hpList : (List.ofFn u.val)[pList.val] ≠ k := by
    simpa only [pList, List.getElem_ofFn] using hu
  exact IntervalCuts.substitute_prefix_length_at_non_slot k (List.ofFn u.val)
    (r.segments v.val) pList hpList

/-- 元の残り色のブロックの最初と最後は同じ一文字の位置（BF §2.2.6）。 -/
lemma compositeFirstPosition_eq_last_of_non_slot {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    compositeFirstPosition u v k r p = compositeLastPosition u v k r p := by
  apply Fin.ext
  change compositePrefixLength u v k r p.val = compositePrefixLength u v k r (p.val + 1) - 1
  rw [compositePrefixLength_at_non_slot u v k r p hp]
  omega

/-- C451f：同じ合成位置の文字は、元の残り色の番号変更だけ（BF §2.2.6）。 -/
lemma positiveCompositeFirstPosition_label {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (p : Fin (m + d + 1)) (hp : (positiveWord u).val p ≠ k) :
    (positiveCompositeCutWord u v k r).val (compositeFirstPosition u v k r p) =
      BarrattEccles.remainingPosition m (n + 1) k ⟨(positiveWord u).val p, hp⟩ := by
  let p' : Fin ((m + 1) + d) := ⟨p.val, by have h := p.isLt; omega⟩
  have hw : (positiveWord u).val p = u.val p' := by
    unfold positiveWord
    exact word_eq_mp_value (by omega : (m + 1) + d = m + d + 1) u p p' rfl
  have hu : u.val p' ≠ k := fun h => hp (hw.trans h)
  calc
    _ = (Surjection.compositeBasisWord u v k r (by omega)).val
        (IntervalCuts.compositeOuterPosition u v k r p' hu) := by
      unfold positiveCompositeCutWord
      exact word_eq_mp_value (by omega) _ _ _ rfl
    _ = BarrattEccles.remainingPosition m (n + 1) k ⟨u.val p', hu⟩ :=
      IntervalCuts.compositeBasisWord_outerPosition u v k r (by omega) p' hu
    _ = _ := congrArg (BarrattEccles.remainingPosition m (n + 1) k) (Subtype.ext hw.symm)

end SerrePositivity.EInfinity.SimplexCuts
