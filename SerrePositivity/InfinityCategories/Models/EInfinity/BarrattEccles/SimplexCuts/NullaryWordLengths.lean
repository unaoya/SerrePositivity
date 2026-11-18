module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryRawValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOccurrencePosition

/-!
模型。文献の定義との比較は後で
# 実際の空語合成の語長と同じ削除位置の移送

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §355。
元のraw合成語・指定位置・有限添字の値を保つ等式移送だけを使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 異なる有限上界でも同じ位置番号を飛ばすと同じ値（BF §1.2.4の添字法則）。 -/
lemma succAbove_val_eq_of_vals {l l' : ℕ} (p : Fin (l + 1)) (p' : Fin (l' + 1))
    (i : Fin l) (i' : Fin l') (hp : p.val = p'.val) (hi : i.val = i'.val) :
    (p.succAbove i).val = (p'.succAbove i').val := by
  simp only [Fin.succAbove, apply_ite Fin.val, Fin.lt_def, Fin.val_castSucc,
    Fin.val_succ, hp, hi]

/-- 語長の等式移送は同じ唯一の出現位置を保つ（BF §1.2.4）。 -/
lemma word_eq_mp_unique {r l l' : ℕ} (h : l = l') (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r l)
    (p : Fin l) (k : Fin r) (hp : v.val p = k) (hu : ∀ j, v.val j = k → j = p) :
    (Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r L) h) v).val (Fin.cast h p) = k ∧
      ∀ j, (Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r L) h) v).val j = k →
        j = Fin.cast h p := by
  subst l'
  exact ⟨hp, hu⟩

/-- 実際のraw合成語の値は、語長を移しても元の同じ一出現削除（BF §2.2.6）。 -/
lemma nullaryRawWord_eq_mp_erase_value {m d N : ℕ} (hN : m + d = N + 1)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (ν : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) 0)
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord m d) (hw : w.val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ)
    (p : Fin (m + 1 + d)) (hu : ∀ j, u.val j = k → j = p) (i : Fin (N + 1)) :
    let V := Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (m + 1) L)
      (by omega : (m + 1) + d = N + 2)) u
    let W := Eq.mp (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word m L) hN) w
    let P : Fin (N + 2) := Fin.cast (by omega) p
    k.succAbove (W.val i) = V.val (P.succAbove i) := by
  let j : Fin (m + d) := Fin.cast hN.symm i
  let P : Fin (N + 2) := Fin.cast (by omega) p
  let Q : Fin (m + d + 1) := Fin.cast (by omega) p
  let b : Fin (m + 1 + d) := Fin.cast (by omega) (Q.succAbove j)
  have hsmall := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value hN w i j rfl
  have hbig := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value (by omega : (m + 1) + d = N + 2) u
    (P.succAbove i) b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.succAbove_val_eq_of_vals P Q i j rfl rfl)
  calc
    _ = k.succAbove (w.val j) := congrArg k.succAbove hsmall
    _ = k.succAbove (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nullaryRawWord u ν k ρ j) :=
      congrArg k.succAbove (congrFun hw j)
    _ = u.val b := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryRawWord_erase_value u ν k ρ p hu j
    _ = _ := hbig.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
