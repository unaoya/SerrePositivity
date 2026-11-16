module

public import SerrePositivity.EInfinity.Surjection.SegmentDegrees

/-!
# 元の合成指数と外側の接頭区切りの補和

Berger–Fresse §1.2.5・§2.2.6、M14 L12a のC452。
元の成分次数の総和と、元の外側区切り順位の補数をそのまま足す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の合成指数と同じ接頭区切りの重み付き和はd*e（BF §1.2.5）。 -/
lemma compositionExponent_add_prefixRanks {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) (n + e)) :
    Surjection.compositionExponent u v k r +
        ∑ i, Surjection.segmentDegree v.val r i *
          Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i) = d * e := by
  have hbound (i : Fin (Surjection.occurrenceCount u.val k)) :
      Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i) ≤ d := by
    let p := Surjection.occurrenceAt u.val k i
    have h := Surjection.lineRank_mono u.val
      (show p.val ≤ (m + 1) + d - 1 by have hp := p.isLt; omega)
    rw [Surjection.lineRank_last] at h
    exact h
  unfold Surjection.compositionExponent
  rw [← Finset.sum_add_distrib]
  have heq : (∑ i, (Surjection.segmentDegree v.val r i *
        (d - Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i)) +
        Surjection.segmentDegree v.val r i *
          Surjection.caesuraRank u.val (Surjection.occurrenceAt u.val k i))) =
      ∑ i, Surjection.segmentDegree v.val r i * d := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.mul_add, Nat.sub_add_cancel (hbound i)]
  rw [heq, ← Finset.sum_mul, Surjection.sum_segmentDegree v r (Surjection.occurrenceCount_pos u k)]
  exact Nat.mul_comm _ _

end SerrePositivity.EInfinity.SimplexCuts
