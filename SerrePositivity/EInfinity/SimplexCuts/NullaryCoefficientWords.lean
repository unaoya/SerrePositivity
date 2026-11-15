module

public import SerrePositivity.EInfinity.IntervalCuts.NullaryRawWord
public import SerrePositivity.EInfinity.Surjection.NullaryErasure

/-!
# 元の空語合成係数と実際のraw語の正規化

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §355。
元のcompositeGeneratorと同じraw合成語を基底または零へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同じ非退化raw合成語を表す基底は元の係数合成そのもの（BF §1.2.4）。 -/
lemma compositionOnWords_nullary_eq_basis_of_raw (A : Type u) [CommRing A] {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (w : Surjection.BasisWord m d) (hw : w.val = IntervalCuts.nullaryRawWord u ν k ρ) :
    Surjection.compositionOnWords A u ν k = Surjection.basis A m d (ULift.up w) := by
  rw [Surjection.compositionOnWords_nullary_of_count_eq_one A u ν k ρ.count_eq_one_of_empty]
  rw [← Surjection.compositeGenerator_nullary A u ν k ρ]
  rw [IntervalCuts.compositeGenerator_nullaryRawWord, ← hw, Surjection.generator_word]

/-- 退化した実際のraw空語合成は元の正規化で零（BF §1.2.4）。 -/
lemma compositionOnWords_nullary_eq_zero_of_raw_degenerate (A : Type u) [CommRing A] {m d : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (h : ¬Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k ρ)) :
    Surjection.compositionOnWords A u ν k = 0 := by
  rw [Surjection.compositionOnWords_nullary_of_count_eq_one A u ν k ρ.count_eq_one_of_empty]
  rw [← Surjection.compositeGenerator_nullary A u ν k ρ]
  rw [IntervalCuts.compositeGenerator_nullaryRawWord]
  exact Surjection.generator_eq_zero_of_not_nondegenerate A _ h

end SerrePositivity.EInfinity.SimplexCuts
