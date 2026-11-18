module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SegmentDegrees

/-!
模型。文献の定義との比較は後で
# 元の合成指数と外側の接頭区切りの補和

Berger–Fresse §1.2.5・§2.2.6、M14 L12a のC452。
元の成分次数の総和と、元の外側区切り順位の補数をそのまま足す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の合成指数と同じ接頭区切りの重み付き和はd*e（BF §1.2.5）。 -/
lemma compositionExponent_add_prefixRanks {m n d e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExponent u v k r +
        ∑ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i *
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i) = d * e := by
  have hbound (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k)) :
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i) ≤ d := by
    let p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_mono u.val
      (show p.val ≤ (m + 1) + d - 1 by have hp := p.isLt; omega)
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_last] at h
    exact h
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExponent
  rw [← Finset.sum_add_distrib]
  have heq : (∑ i, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i *
        (d - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i)) +
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i *
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i))) =
      ∑ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree v.val r i * d := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.mul_add, Nat.sub_add_cancel (hbound i)]
  rw [heq, ← Finset.sum_mul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sum_segmentDegree v r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount_pos u k)]
  exact Nat.mul_comm _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
