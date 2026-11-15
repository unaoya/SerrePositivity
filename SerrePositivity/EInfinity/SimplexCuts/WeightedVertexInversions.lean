module

public import SerrePositivity.EInfinity.SimplexCuts.ActiveVertexCounts
public import SerrePositivity.EInfinity.SimplexCuts.ColorSortingBoundarySigns

/-!
# 活動頂点の逆転数と区間の重み付き逆転数

Berger–Fresse §2.2.4・§2.2.7、M14 L09a。
既存の逆転数を水平座標のfiberでまとめ、区間の符号次数との一致を示す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open SerrePositivity.EInfinity.IntervalCuts (positionInversionTerm positionInversionCount)

lemma inversion_condition_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (x y : Fin N) :
    (x < y ∧ v (f y) < v (f x)) ↔ (f x < f y ∧ v (f y) < v (f x)) := by
  constructor
  · rintro ⟨hxy, hv⟩
    refine ⟨lt_of_le_of_ne (f.monotone hxy.le) ?_, hv⟩
    intro he
    rw [he] at hv
    exact (lt_irrefl _) hv
  · rintro ⟨hf, hv⟩
    refine ⟨?_, hv⟩
    by_contra h
    exact (not_le_of_gt hf) (f.monotone (le_of_not_gt h))

lemma positionInversionTerm_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (x y : Fin N) :
    positionInversionTerm (v ∘ f) x y = if f x < f y ∧ v (f y) < v (f x) then 1 else 0 := by
  unfold positionInversionTerm
  simp only [Function.comp_apply, inversion_condition_comp_monotone]

/-- C106：単調な位置のfiberでまとめた逆転数は、fiberの濃度の重み付き逆転数。 -/
lemma positionInversionCount_comp_monotone {N M r : ℕ} (f : Fin N →o Fin M)
    (v : Fin M → Fin r) (s : Finset (Fin N)) :
    positionInversionCount (v ∘ f) s =
      ∑ i : Fin M, ∑ j : Fin M, if i < j ∧ v j < v i then
        (s.filter (fun x => f x = i)).card * (s.filter (fun y => f y = j)).card else 0 := by
  have hy (x : Fin N) : (∑ y ∈ s, positionInversionTerm (v ∘ f) x y) =
      ∑ j : Fin M, if f x < j ∧ v j < v (f x) then (s.filter (fun y => f y = j)).card else 0 := by
    have h := Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.univ) (g := f)
      (fun _ _ => Finset.mem_univ _) (fun y => positionInversionTerm (v ∘ f) x y)
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    have hc : ∀ y ∈ s.filter (fun y => f y = j),
        positionInversionTerm (v ∘ f) x y = if f x < j ∧ v j < v (f x) then 1 else 0 := by
      intro y hy
      rw [positionInversionTerm_comp_monotone, (Finset.mem_filter.mp hy).2]
    rw [Finset.sum_congr rfl hc, Finset.sum_const]
    split_ifs <;> simp
  unfold positionInversionCount
  simp_rw [hy]
  have h := Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.univ) (g := f)
    (fun _ _ => Finset.mem_univ _) (fun x =>
      ∑ j : Fin M, if f x < j ∧ v j < v (f x) then (s.filter (fun y => f y = j)).card else 0)
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hc : ∀ x ∈ s.filter (fun x => f x = i),
      (∑ j : Fin M, if f x < j ∧ v j < v (f x) then (s.filter (fun y => f y = j)).card else 0) =
      ∑ j : Fin M, if i < j ∧ v j < v i then (s.filter (fun y => f y = j)).card else 0 := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

/-- C107：BFの区間の重み付き逆転指数は、展開した活動頂点の逆転数。 -/
lemma permutationExponent_eq_active_inversions {m q r : ℕ} (s : Cut m q)
    (v : Fin (m + 1) → Fin r) :
    permutationExponent s v = positionInversionCount (label s v) (activeVertexPositions s v) := by
  have h := positionInversionCount_comp_monotone s.horizontal v (activeVertexPositions s v)
  simp_rw [active_fiber_card] at h
  exact h.symm

end SerrePositivity.EInfinity.SimplexCuts
