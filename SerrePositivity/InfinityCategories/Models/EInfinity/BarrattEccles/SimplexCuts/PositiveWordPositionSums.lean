module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOccurrenceSums

/-!
模型。文献の定義との比較は後で
# 元の全位置と残り位置・指定色の出現の和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
同じ位置の有限和を二つへ分け、指定色の位置を元の出現番号で読む。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 元の全位置の和を、残り位置と同じ指定色の出現番号で読む（BF §2.2.6）。 -/
lemma positiveWord_position_sum {m d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (F : Fin (m + d + 1) → ℕ) :
    (∑ p, F p) =
      (∑ p : {p : Fin (m + d + 1) // (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k}, F p.val) +
      ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) := by
  classical
  let e : {p : Fin (m + d + 1) // ¬(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k} ≃
      ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k) :=
    Equiv.subtypeEquivRight (fun p => by simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences])
  have he : (∑ p : {p : Fin (m + d + 1) // ¬(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k}, F p.val) =
      ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) := by
    calc
      _ = ∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k), F p.val := by
        apply Fintype.sum_equiv e
        intro p
        rfl
      _ = _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_slot_position_sum u k F
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun p : Fin (m + d + 1) => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p ≠ k) F
  simp only [he] at hs
  exact hs.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
