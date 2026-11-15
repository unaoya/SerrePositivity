module

public import SerrePositivity.EInfinity.SimplexCuts.CrossIntervalPrefixModeq
public import SerrePositivity.EInfinity.SimplexCuts.NestedPrefixDegreeSum
public import SerrePositivity.EInfinity.SimplexCuts.ColorRankIntervals

/-!
# 同じ合成切断の他色の先行活動頂点数

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
元の外側区間の同じ最初の色別順位でB_iを読み、元の交差寄与と照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の外側の指定区間より先行する、同じ他色の活動頂点数（BF §2.2.6）。 -/
def positiveCompositeOtherActivePrefix {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) : ℕ :=
  let δ := positiveCompositeOuterCut u v k c
  let j := colorIntervalFirst δ (positiveWord u) k (positiveOccurrencePosition u k i)
    (positiveOccurrencePosition_value u k i)
  ((activeVertexPositions δ (positiveWord u).val).filter (fun z =>
    z < colorPositionEquiv δ (positiveWord u) ⟨k, j⟩ ∧ label δ (positiveWord u).val z ≠ k)).card

/-- 元の外側交差寄与は、同じB_iと前方総次数に合同（BF §2.2.6）。 -/
lemma positiveComposite_crossWeight_modeq {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q)
    (i : Fin (Surjection.occurrenceCount u.val k)) :
    Nat.ModEq 2
      (∑ p : {p : Fin (m + d + 1) // (positiveWord u).val p ≠ k},
        (IntervalCuts.positionInversionTerm (positiveWord u).val p.val
            (positiveOccurrencePosition u k i) +
          IntervalCuts.positionInversionTerm (positiveWord u).val
            (positiveOccurrencePosition u k i) p.val) *
          intervalLength (positiveCompositeOuterCut u v k c) (positiveWord u).val p.val)
      (positiveCompositeOtherActivePrefix u v k c i +
        positiveNestedPrefixDegree u k (positiveCompositeOuterCut u v k c)) := by
  let δ := positiveCompositeOuterCut u v k c
  let w := positiveWord u
  let p := positiveOccurrencePosition u k i
  let j := colorIntervalFirst δ w k p (positiveOccurrencePosition_value u k i)
  let x := colorPositionEquiv δ w ⟨k, j⟩
  have hm : j ∈ colorIntervalRanks δ w k p :=
    (colorIntervalRanks δ w k p).min'_mem
      (colorIntervalRanks_nonempty δ w k p (positiveOccurrencePosition_value u k i))
  have hx : δ.horizontal x = p := by
    dsimp only [x]
    rw [colorPositionEquiv_apply]
    exact (Finset.mem_filter.mp hm).2
  have hN := cross_intervalLength_modeq_prefix δ w k p
    (positiveOccurrencePosition_value u k i) x hx
  simpa only [positiveCompositeOtherActivePrefix,
    positiveNestedPrefixDegree_eq_prefixOutputDegree, δ, w, p, j, x] using hN

end SerrePositivity.EInfinity.SimplexCuts
