module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.RecoveredNestedPartition

/-!
模型。文献の定義との比較は後で
# 復元した同じ重なる分割の部分長

Berger–Fresse §1.2.4・§2.2.6、M14 L12a。
元の出現数の等式移送を保ち、復元した分割の値を同じ端点の差として読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C375：同じ分割数の等式移送は、同じ番号の部分長を保つ（BF §1.2.4）。 -/
lemma overlap_eq_mp_val {t t' L : ℕ} (h : t = t') (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t L)
    (i : Fin t') (j : Fin t) (hij : i.val = j.val) :
    ((Eq.mp (congrArg (fun k => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition k L) h) r).val i).val =
      (r.val j).val := by
  subst t'
  have he : i = j := Fin.ext hij
  subst i
  rfl

/-- C376：復元した部分長は、指定した元の二端点の差に一を足した値（BF §2.2.6）。 -/
lemma positiveNestedPartition_length {m n d e q : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveNestedCutIndex u v k q) (i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k)) (hij : i.val = j.val) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPartition u v k c).val i).val =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nestedSegmentEnd c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k c.2 j -
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nestedSegmentStart c.1 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u) k c.2 j + 1 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveNestedPartition
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.overlap_eq_mp_val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_occurrenceCount u k) _ i j hij

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
