module

public import SerrePositivity.EInfinity.SimplexCuts.OccurrenceCardinalities
public import SerrePositivity.EInfinity.SimplexCuts.CompositeFirstPositionOrder
public import SerrePositivity.EInfinity.SimplexCuts.CompositeRemainingPositions
public import SerrePositivity.EInfinity.SimplexCuts.PositiveNestedCuts
public import SerrePositivity.EInfinity.IntervalCuts.SubstitutionCounts
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Fintype.EquivFin

/-!
# 元の残り色の全出現位置の順序同値

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の指定面の照合。
元の文字の出現回数と同じ接頭位置を保ち、有限濃度によって全出現を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の残り色の出現回数は、同じ合成語でも変わらない（BF §2.2.6）。 -/
lemma positiveCompositeWord_remaining_count {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    Surjection.occurrenceCount (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a) =
      Surjection.occurrenceCount (positiveWord u).val a.val := by
  unfold Surjection.occurrenceCount
  rw [positiveCompositeCutWord_list]
  change (Surjection.substitute k (List.ofFn u.val) (r.segments v.val)).count
    (BarrattEccles.remainingPosition m (n + 1) k a) = _
  rw [IntervalCuts.remaining_count_substitute]
  exact (positiveWord_occurrenceCount u a.val).symm

/-- 元の残り色の全出現位置を、同じ合成ブロックの最初の位置へ送る順序同値（BF §2.2.6）。 -/
def remainingWordPositionOrderIso {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) ((n + 1) + e))
    (a : {a : Fin (m + 1) // a ≠ k}) :
    ↥(Surjection.occurrences (positiveWord u).val a.val) ≃o
      ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a)) := by
  let f : ↥(Surjection.occurrences (positiveWord u).val a.val) →
      ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a)) := fun p =>
    ⟨compositeFirstPosition u v k r p.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have hp : (positiveWord u).val p.val = a.val := (Finset.mem_filter.mp p.property).2
      have hpk : (positiveWord u).val p.val ≠ k := fun h => a.property (hp.symm.trans h)
      exact (positiveCompositeFirstPosition_label u v k r p.val hpk).trans
        (congrArg (BarrattEccles.remainingPosition m (n + 1) k) (Subtype.ext hp))⟩⟩
  have hf : StrictMono f := by
    intro p p' h
    exact compositeFirstPosition_strictMono u v k r h
  have hc : Fintype.card ↥(Surjection.occurrences (positiveWord u).val a.val) =
      Fintype.card ↥(Surjection.occurrences (positiveCompositeCutWord u v k r).val
        (BarrattEccles.remainingPosition m (n + 1) k a)) := by
    simp only [Fintype.card_coe, occurrences_card_eq_count]
    exact (positiveCompositeWord_remaining_count u v k r a).symm
  have hb := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf.injective, hc⟩
  exact StrictMono.orderIsoOfSurjective f hf hb.2

end SerrePositivity.EInfinity.SimplexCuts
