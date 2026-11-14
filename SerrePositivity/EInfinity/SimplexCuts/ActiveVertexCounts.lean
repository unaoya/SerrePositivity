module

public import SerrePositivity.EInfinity.SimplexCuts.ExpandedCaesuras

/-!
# 展開色列の活動頂点の濃度

Berger–Fresse §2.2.3–4・§2.2.7、M14 L09a。
各色の最後の一頂点を除いた有限集合を、区間の符号次数と出力次数で数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 後に同色の頂点を持つ経路の頂点。元の語の非退化性は要求しない。 -/
def activeVertexPositions {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r) :
    Finset (Fin (m + q + 1)) := Finset.univ.filter (Surjection.Caesura (label s v))

/-- C102：区間ごとの活動頂点数は区間の符号次数。 -/
lemma active_fiber_card {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (i : Fin (m + 1)) :
    ((activeVertexPositions s v).filter (fun j => s.horizontal j = i)).card =
      intervalLength s v i := by
  have he : (activeVertexPositions s v).filter (fun j => s.horizontal j = i) =
      (intervalPositions s i).filter (Surjection.Caesura (label s v)) := by
    ext j
    simp only [activeVertexPositions, intervalPositions, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact and_comm
  rw [he, interval_active_card]

/-- C103：一色の活動頂点数は、同じ色の区間の重みの和。 -/
lemma active_color_card_eq_sum {m q r : ℕ} (s : Cut m q) (v : Fin (m + 1) → Fin r)
    (c : Fin r) :
    ((activeVertexPositions s v).filter (fun j => label s v j = c)).card =
      ∑ i ∈ Surjection.occurrences v c, intervalLength s v i := by
  have ht := Finset.card_eq_sum_card_fiberwise
    (f := s.horizontal)
    (s := (activeVertexPositions s v).filter (fun j => label s v j = c))
    (t := Surjection.occurrences v c)
    (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
  refine ht.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  have hv : v i = c := (Finset.mem_filter.mp hi).2
  have he : ((activeVertexPositions s v).filter (fun j => label s v j = c)).filter
      (fun j => s.horizontal j = i) =
      (activeVertexPositions s v).filter (fun j => s.horizontal j = i) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, _⟩, hj⟩
      exact ⟨ha, hj⟩
    · rintro ⟨ha, hj⟩
      refine ⟨⟨ha, ?_⟩, hj⟩
      change v (s.horizontal j) = c
      rw [hj]
      exact hv
  rw [he, active_fiber_card]

/-- C104：全射語では一色の活動頂点数は実際の出力次数。 -/
lemma active_color_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1))
    (c : Fin r) :
    ((activeVertexPositions s v.val).filter (fun j => label s v.val j = c)).card =
      outputDegree s v c := by
  rw [active_color_card_eq_sum, outputDegree_eq_sum_intervalLength]

/-- C105：活動頂点の全数は、実際の全出力次数。 -/
lemma activeVertexPositions_card {m q r : ℕ} (s : Cut m q) (v : Surjection.Word r (m + 1)) :
    (activeVertexPositions s v.val).card = m + q + 1 - r := by
  have ht := Finset.card_eq_sum_card_fiberwise
    (f := label s v.val) (s := activeVertexPositions s v.val) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [ht]
  simp_rw [active_color_card]
  exact outputDegree_sum s v

end SerrePositivity.EInfinity.SimplexCuts
