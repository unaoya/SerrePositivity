module

public import SerrePositivity.EInfinity.SimplexCuts.RecoveredNestedPartition

/-!
# 復元した同じ重なる分割の部分長

Berger–Fresse §1.2.4・§2.2.6、M14 L12a。
元の出現数の等式移送を保ち、復元した分割の値を同じ端点の差として読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C375：同じ分割数の等式移送は、同じ番号の部分長を保つ（BF §1.2.4）。 -/
lemma overlap_eq_mp_val {t t' L : ℕ} (h : t = t') (r : Surjection.OverlapPartition t L)
    (i : Fin t') (j : Fin t) (hij : i.val = j.val) :
    ((Eq.mp (congrArg (fun k => Surjection.OverlapPartition k L) h) r).val i).val =
      (r.val j).val := by
  subst t'
  have he : i = j := Fin.ext hij
  subst i
  rfl

/-- C376：復元した部分長は、指定した元の二端点の差に一を足した値（BF §2.2.6）。 -/
lemma positiveNestedPartition_length {m n d e q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (v : Surjection.BasisWord (n + 1) e) (k : Fin (m + 1))
    (c : PositiveNestedCutIndex u v k q) (i : Fin (Surjection.occurrenceCount u.val k))
    (j : Fin (Surjection.occurrenceCount (positiveWord u).val k)) (hij : i.val = j.val) :
    ((positiveNestedPartition u v k c).val i).val =
      nestedSegmentEnd c.1 (positiveWord u) k c.2 j -
        nestedSegmentStart c.1 (positiveWord u) k c.2 j + 1 := by
  unfold positiveNestedPartition
  exact overlap_eq_mp_val (positiveWord_occurrenceCount u k) _ i j hij

end SerrePositivity.EInfinity.SimplexCuts
