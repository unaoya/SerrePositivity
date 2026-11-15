module

public import SerrePositivity.EInfinity.SimplexCuts.CutGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.OccurrenceCardinalities
public import SerrePositivity.EInfinity.SimplexCuts.Signs

/-!
# 同じ空語合成の切断添字と語長の移送

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §356。
元の唯一の出現位置と全切断和を、同じ自然数の等式によって移す。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open SerrePositivity.TensorPowers
open scoped Simplicial

/-- 一出現の元の有限語には同じ唯一の位置がある（BF §1.2.4）。 -/
lemma unique_position_of_occurrenceCount_one {r l : ℕ} (w : Fin l → Fin r) (k : Fin r)
    (h : Surjection.occurrenceCount w k = 1) :
    ∃ p : Fin l, w p = k ∧ ∀ j, w j = k → j = p := by
  have hc : (Surjection.occurrences w k).card = 1 := by rw [occurrences_card_eq_count, h]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have hm : p ∈ Surjection.occurrences w k := by rw [hp]; exact Finset.mem_singleton_self p
  refine ⟨p, (Finset.mem_filter.mp hm).2, ?_⟩
  intro j hj
  apply Finset.mem_singleton.mp
  rw [← hp]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩

/-- 語長を二度移しても同じ元の語を一度移したもの（BF §1.2.4の型の移送）。 -/
lemma word_eq_mp_trans {r l l' l'' : ℕ} (h : l = l') (h' : l' = l'')
    (w : Surjection.Word r l) :
    Eq.mp (congrArg (fun L => Surjection.Word r L) h')
      (Eq.mp (congrArg (fun L => Surjection.Word r L) h) w) =
      Eq.mp (congrArg (fun L => Surjection.Word r L) (h.trans h')) w := by
  subst l''
  subst l'
  rfl

/-- 同じ切断区間数を等式で移しても、元の符号付き全和は同じ（BF §2.2.6）。 -/
lemma sum_cutGenerator_terms_eq_mp (A : Type u) [CommRing A] (S : SSet.{0})
    {M : Type v} [AddCommGroup M] {m n q r : ℕ} (h : m = n)
    (w : Surjection.Word r (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -((m + q + 1 - r : ℕ) : ℤ) = z)
    (T : (power (chains A S) r).X z → M) :
    (∑ s : Cut m q, cutSign s w.val • T
      (vectorTensorAt (chains A S) r (cutGeneratorFamily A S s w x) z
        (by rw [vectorDegree_cutGeneratorFamily]; exact hz))) =
      ∑ s : Cut n q,
        cutSign s (Eq.mp (congrArg (fun L => Surjection.Word r (L + 1)) h) w).val • T
          (vectorTensorAt (chains A S) r
            (cutGeneratorFamily A S s
              (Eq.mp (congrArg (fun L => Surjection.Word r (L + 1)) h) w) x) z
            (by rw [vectorDegree_cutGeneratorFamily]; rw [← h]; exact hz)) := by
  subst n
  rfl

end SerrePositivity.EInfinity.SimplexCuts
