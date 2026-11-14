module

public import SerrePositivity.EInfinity.SimplexCuts.ActiveVertexCounts
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# 元の活動頂点の水平条件の濃度と区間長

Berger–Fresse §2.2.4・§2.2.6、M14 L12a の C452。
同じ水平 fiber の濃度を既存 intervalLength で数える。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の水平条件で選んだ活動頂点数は、同じ区間長の和（BF §2.2.4）。 -/
lemma active_filter_horizontal_card {m q r : ℕ} (s : Cut m q)
    (w : Fin (m + 1) → Fin r) (P : Fin (m + 1) → Prop) [DecidablePred P] :
    ((activeVertexPositions s w).filter (fun z => P (s.horizontal z))).card =
      ∑ j : Fin (m + 1), if P j then intervalLength s w j else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h := Finset.sum_fiberwise_of_maps_to
    (s := activeVertexPositions s w) (t := Finset.univ) (g := s.horizontal)
    (fun _ _ => Finset.mem_univ _) (fun z => if P (s.horizontal z) then (1 : ℕ) else 0)
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  have hc : ∀ z ∈ (activeVertexPositions s w).filter (fun z => s.horizontal z = j),
      (if P (s.horizontal z) then 1 else 0 : ℕ) = if P j then 1 else 0 := by
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, active_fiber_card]
  split_ifs <;> simp

end SerrePositivity.EInfinity.SimplexCuts
