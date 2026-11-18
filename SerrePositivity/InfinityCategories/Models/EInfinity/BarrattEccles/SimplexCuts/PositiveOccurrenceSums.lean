module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PositiveOccurrenceCaesuras
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
模型。文献の定義との比較は後で
# 元の指定色の全出現位置の和

Berger–Fresse §1.2.4・§2.2.6、M14 L12a の C452。
同じ語長で読んだ元の全出現を、その元の出現番号へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同じ語長で読んだ指定色の全出現も、元の番号の一つ（BF §1.2.4）。 -/
lemma positiveOccurrencePosition_complete {m d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (k : Fin (m + 1))
    (p : Fin (m + d + 1)) (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val p = k) :
    ∃ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i = p := by
  let p' : Fin ((m + 1) + d) := ⟨p.val, by have hb := p.isLt; omega⟩
  have hv : u.val p' = k :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.word_eq_mp_value (by omega : (m + 1) + d = m + d + 1) u p p' rfl).symm.trans hp
  obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt_complete u.val k p' hv
  refine ⟨i, Fin.ext ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt u.val k i).val = p.val
  exact congrArg (fun x : Fin ((m + 1) + d) => x.val) hi

/-- 元の指定色の全出現の和は、同じ出現番号の和（BF §2.2.6）。 -/
lemma positiveWord_slot_position_sum {m d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (k : Fin (m + 1)) (F : Fin (m + d + 1) → ℕ) :
    (∑ p : ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k), F p.val) =
      ∑ i : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k), F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i) := by
  let f : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) →
      ↥(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord u).val k) := fun i =>
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_value u k i⟩⟩
  have hi : Function.Injective f := by
    intro i j he
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_strictMono u k).injective (congrArg Subtype.val he)
  have hs : Function.Surjective f := by
    intro p
    obtain ⟨i, hi⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition_complete u k p.val
      (Finset.mem_filter.mp p.property).2
    exact ⟨i, Subtype.ext hi⟩
  have h := Fintype.sum_bijective f ⟨hi, hs⟩ (fun i => F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveOccurrencePosition u k i))
    (fun p => F p.val) (fun _ => rfl)
  exact h.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
