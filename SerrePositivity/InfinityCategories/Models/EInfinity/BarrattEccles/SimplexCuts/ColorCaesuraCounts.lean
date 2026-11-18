module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.PrefixCaesuras
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
模型。文献の定義との比較は後で
# 各色の区切り位置の個数

Berger–Fresse §1.2.2・§2.2.3–4、M14 L09a。
既存の最後の出現のAPIから、各色の全出現のうち最後以外を数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C93：同じ色のcaesuraは、その色の最後の出現より前にある位置。 -/
lemma caesura_iff_lt_lastOccurrence {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l)
    (c : Fin n) (i : Fin l) (hi : u.val i = c) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i ↔ i < u.lastOccurrence c := by
  constructor
  · rintro ⟨j, hij, hj⟩
    have hm : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.trans hi⟩
    exact lt_of_lt_of_le hij ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c).le_max' j hm)
  · intro h
    exact ⟨u.lastOccurrence c, h, (u.lastOccurrence_value c).trans hi.symm⟩

/-- C94：同じ色のcaesuraを選ぶことは、最後の一出現を除くこと。 -/
lemma caesura_filter_occurrences {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (c : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c).filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c).erase (u.lastOccurrence c) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hi, hc⟩
    refine ⟨?_, hi⟩
    intro he
    exact u.not_caesura_lastOccurrence c (he ▸ hc)
  · rintro ⟨hne, hi⟩
    refine ⟨hi, ?_⟩
    have hv : u.val i = c := (Finset.mem_filter.mp hi).2
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_iff_lt_lastOccurrence u c i hv).mpr
    exact lt_of_le_of_ne ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c).le_max' i hi) hne

/-- C95：各色のcaesuraの数に一を足すと、その色の全出現数。 -/
lemma sum_caesura_occurrences_add_one {n l : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (c : Fin n) :
    (∑ i ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c, if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val i then 1 else 0) + 1 =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c).card := by
  rw [← Finset.card_filter, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.caesura_filter_occurrences]
  have hm : u.lastOccurrence c ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrences u.val c :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.lastOccurrence_value c⟩
  rw [Finset.card_erase_of_mem hm]
  have hp := Finset.card_pos.mpr (u.occurrences_nonempty c)
  omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
