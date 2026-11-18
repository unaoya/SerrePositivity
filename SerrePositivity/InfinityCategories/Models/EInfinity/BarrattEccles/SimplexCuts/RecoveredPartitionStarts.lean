module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.RecoveredPartitionValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OverlapIntervalStarts

/-!
模型。文献の定義との比較は後で
# 同じ二段切断から復元した分割の始点

Berger–Fresse §2.2.6、M14 L12a。
元の出現数の等式移送を保ち、同じ分割の開始位置を読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C419：同じ分割数の移送では、元の開始位置も変わらない（BF §1.2.4）。 -/
lemma overlap_eq_mp_start {t t' L : ℕ} (h : t = t') (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (i : Fin t') (j : Fin t) (hij : i.val = j.val) :
    (Eq.mp (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition k L) h) r).start i = r.start j := by
  subst t'
  have he : i = j := Fin.ext hij
  subst i
  rfl

/-- C420：復元した同じ分割の開始位置は、指定した元の端点（BF §2.2.6）。 -/
lemma positiveNestedPartition_start {m n d e q : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q) (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k)) (hij : i.val = j.val) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPartition u v k c).start i =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nestedSegmentStart c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k c.2 j := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPartition
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_mp_start (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_occurrenceCount u k) _ i j hij]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlapOfIntervals_start _ _ _ _ _ _ _ _ j

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
