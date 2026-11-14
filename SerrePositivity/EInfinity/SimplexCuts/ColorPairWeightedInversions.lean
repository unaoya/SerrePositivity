module

public import SerrePositivity.EInfinity.SimplexCuts.MixedVertexInversionFibers
public import SerrePositivity.EInfinity.Surjection.OccurrenceOrder

/-!
# 色別の重み付き逆転和と活動頂点の逆転和

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ水平 fiber の濃度により、元の語の位置と元の活動頂点で数えた式を結ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 二条件で制限した同じ対の有限和をfilterへ書き直す（BF §2.2.4 の補助）。 -/
lemma sum_ite_and_eq_filter {α β : Type*} (S : Finset α) (T : Finset β)
    (P : α → Prop) (Q : β → Prop) [DecidablePred P] [DecidablePred Q]
    (F : α → β → ℕ) :
    (∑ x ∈ S, ∑ y ∈ T, if P x ∧ Q y then F x y else 0) =
      ∑ x ∈ S.filter P, ∑ y ∈ T.filter Q, F x y := by
  classical
  simp only [Finset.sum_filter, ite_and]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

/-- 同じ色と水平位置を持つ活動頂点数は元の区間長（BF §2.2.4）。 -/
lemma active_color_horizontal_fiber_card {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a : Fin r) (i : Fin (m + 1)) :
    (((activeVertexPositions s v).filter (fun x => label s v x = a)).filter
      (fun x => s.horizontal x = i)).card = if v i = a then intervalLength s v i else 0 := by
  have hs : ((activeVertexPositions s v).filter (fun x => label s v x = a)).filter
      (fun x => s.horizontal x = i) =
      if v i = a then (activeVertexPositions s v).filter (fun x => s.horizontal x = i)
      else ∅ := by
    ext x
    by_cases hv : v i = a
    · rw [ite_eq_left hv]
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact ⟨hx.1.1, hx.2⟩
      · intro hx
        refine ⟨⟨hx.1, ?_⟩, hx.2⟩
        change v (s.horizontal x) = a
        rw [hx.2, hv]
    · rw [ite_eq_right hv]
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, hcol⟩, hpos⟩
      apply hv
      change v (s.horizontal x) = a at hcol
      exact hpos ▸ hcol
  rw [hs]
  split_ifs <;> simp only [active_fiber_card, Finset.card_empty]

/-- 部分型の同じ二重和を有限部分集合の和へ書き直す（BF §2.2.4 の補助）。 -/
lemma sum_finset_subtype_pair {α β : Type*} (S : Finset α) (T : Finset β)
    (F : α → β → ℕ) :
    (∑ x : ↥S, ∑ y : ↥T, F x.val y.val) = ∑ x ∈ S, ∑ y ∈ T, F x y := by
  classical
  calc
    _ = ∑ x : ↥S, ∑ y ∈ T, F x.val y := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Finset.sum_subtype T (fun _ => Iff.rfl) (F x.val)).symm
    _ = _ := (Finset.sum_subtype S (fun _ => Iff.rfl) (fun x => ∑ y ∈ T, F x y)).symm

/-- 色別の区間長の逆転和は、同じ活動頂点対の逆転和（BF §2.2.4・6）。 -/
lemma weighted_color_inversion_sum_eq_active {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) (a b : Fin r) :
    (∑ i : ↥(Surjection.occurrences v a), ∑ j : ↥(Surjection.occurrences v b),
      if i.val < j.val ∧ v j.val < v i.val then
        intervalLength s v i.val * intervalLength s v j.val else 0) =
    (∑ x : ↥(colorPositions s v a), ∑ y : ↥(colorPositions s v b),
      if x.val ∈ activeVertexPositions s v ∧ y.val ∈ activeVertexPositions s v then
        IntervalCuts.positionInversionTerm (label s v) x.val y.val else 0) := by
  have h := sum_positionInversionTerm_comp_monotone s.horizontal v
    ((activeVertexPositions s v).filter (fun x => label s v x = a))
    ((activeVertexPositions s v).filter (fun y => label s v y = b))
  simp_rw [active_color_horizontal_fiber_card] at h
  have hlabel : v ∘ s.horizontal = label s v := rfl
  rw [hlabel] at h
  have hf (c : Fin r) : (colorPositions s v c).filter
      (fun x => x ∈ activeVertexPositions s v) =
      (activeVertexPositions s v).filter (fun x => label s v x = c) := by
    ext x
    simp only [colorPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [sum_finset_subtype_pair (Surjection.occurrences v a) (Surjection.occurrences v b)
    (fun i j => if i < j ∧ v j < v i then intervalLength s v i * intervalLength s v j else 0)]
  rw [sum_finset_subtype_pair (colorPositions s v a) (colorPositions s v b)
    (fun x y => if x ∈ activeVertexPositions s v ∧ y ∈ activeVertexPositions s v then
      IntervalCuts.positionInversionTerm (label s v) x y else 0)]
  rw [sum_ite_and_eq_filter, hf a, hf b]
  rw [h]
  simp only [Surjection.occurrences, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : v i = a
  · simp only [hi, ite_true]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : v j = b <;> split_ifs <;> simp_all
  · simp [hi]

end SerrePositivity.EInfinity.SimplexCuts
