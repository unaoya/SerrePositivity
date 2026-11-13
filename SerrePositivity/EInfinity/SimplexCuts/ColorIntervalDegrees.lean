module

public import SerrePositivity.EInfinity.SimplexCuts.IntervalCardinalities
public import SerrePositivity.EInfinity.SimplexCuts.ColorCaesuraCounts

/-!
# 出力次数と区間の符号次数の和

Berger–Fresse §2.2.3–4、M14 L09a。
各色の頂点を区間のfiberに分け、最後以外の出現の一をcaesuraとして数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C96：一つの色の頂点数は、その色の各区間の頂点数の和。 -/
lemma colorPositions_card_by_intervals {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (c : Fin r) :
    (colorPositions s v c).card =
      ∑ i ∈ Surjection.occurrences v c, (intervalPositions s i).card := by
  have ht := Finset.card_eq_sum_card_fiberwise
    (f := s.horizontal) (s := colorPositions s v c) (t := Surjection.occurrences v c)
    (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
  refine ht.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ext j
  have hv : v i = c := (Finset.mem_filter.mp hi).2
  simp only [colorPositions, intervalPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hj⟩
    exact hj
  · intro hj
    refine ⟨?_, hj⟩
    change v (s.horizontal j) = c
    rw [hj]
    exact hv

/-- C97：各色の出力次数は、その色の区間の符号次数を足した値。 -/
lemma outputDegree_eq_sum_intervalLength {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (c : Fin r) :
    outputDegree s v c = ∑ i ∈ Surjection.occurrences v.val c, intervalLength s v.val i := by
  have hc := colorPositions_card_by_intervals s v.val c
  simp_rw [intervalPositions_card] at hc
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one] at hc
  have hf := sum_caesura_occurrences_add_one v c
  have hw : (∑ i ∈ Surjection.occurrences v.val c, intervalLength s v.val i) =
      (∑ i ∈ Surjection.occurrences v.val c, (hi s i - lo s i)) +
      (∑ i ∈ Surjection.occurrences v.val c, if Surjection.Caesura v.val i then 1 else 0) := by
    simp only [intervalLength, Finset.sum_add_distrib]
  unfold outputDegree
  omega

end SerrePositivity.EInfinity.SimplexCuts
