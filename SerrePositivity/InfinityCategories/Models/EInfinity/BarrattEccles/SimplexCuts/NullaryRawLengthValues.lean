module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryWordLengths

/-!
模型。文献の定義との比較は後で
# 退化を許す元のraw空語合成の語長移送

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §361。
基底を選ばず、元のraw語の全位置の値と非退化条件を同じ有限添字で移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ有限添字の等式移送はraw語の隣接非退化条件を保つ（BF §1.2.1）。 -/
lemma raw_nondegenerate_cast_iff {r l l' : ℕ} (h : l = l') (w : Fin l → Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (fun i : Fin l' => w (Fin.cast h.symm i)) ↔
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate w := by
  subst l'
  rfl

/-- 語長を移した退化raw語も、元の同じ一出現削除の値を持つ（BF §2.2.6）。 -/
lemma nullaryRawWord_cast_erase_value {m d N : ℕ} (hN : m + d = N + 1)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (N + 1)) :
    let V := Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (m + 1) L)
      (by omega : (m + 1) + d = N + 2)) u
    let P : Fin (N + 2) := Fin.cast (by omega) p
    k.succAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ (Fin.cast hN.symm i)) =
      V.val (P.succAbove i) := by
  let j : Fin (m + d) := Fin.cast hN.symm i
  let P : Fin (N + 2) := Fin.cast (by omega) p
  let Q : Fin (m + d + 1) := Fin.cast (by omega) p
  let b : Fin (m + 1 + d) := Fin.cast (by omega) (Q.succAbove j)
  have hbig := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value (by omega : (m + 1) + d = N + 2) u
    (P.succAbove i) b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.succAbove_val_eq_of_vals P Q i j rfl rfl)
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryRawWord_erase_value u ν k ρ p hu j).trans hbig.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
