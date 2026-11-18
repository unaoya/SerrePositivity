module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryRawPositions

/-!
模型。文献の定義との比較は後で
# 実際の空語合成の全位置の値

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §332。
元のraw合成語を同じ位置で評価し、指定色を飛ばす同じ順序単射へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 実際の空語のraw合成語は、指定された一出現を消した元の語（BF §2.2.6）。 -/
lemma nullaryRawWord_erase_value {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (m + d)) :
    k.succAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r i) =
      u.val (Fin.cast (by omega : m + d + 1 = m + 1 + d)
        ((Fin.cast (by omega : m + 1 + d = m + d + 1) p).succAbove i)) := by
  let ep : Fin (m + d + 1) := Fin.cast (by omega) p
  let j : Fin (m + 1 + d) := Fin.cast (by omega) (ep.succAbove i)
  have hj : u.val j ≠ k := by
    intro h
    have he := hu j h
    have he' : ep.succAbove i = ep := by
      apply Fin.ext
      have hv : j.val = p.val := congrArg Fin.val he
      exact hv
    exact Fin.succAbove_ne ep i he'
  have hpos : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r j hj = i :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.compositeOuterPosition_nullary_erase u v k r p hu i hj
  calc
    k.succAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r i) =
        k.succAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.compositeOuterPosition u v k r j hj)) :=
      congrArg (fun a => k.succAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u v k r a)) hpos.symm
    _ = u.val j := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord_outerPosition]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.succAbove_remainingPosition_nullary m k ⟨u.val j, hj⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
