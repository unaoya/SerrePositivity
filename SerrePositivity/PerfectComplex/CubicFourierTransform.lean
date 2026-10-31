module

public import SerrePositivity.PerfectComplex.Eigen.Cubic

/-! # The Fourier transform and its inverse on three scalar coordinates -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- The linear map represented by a three-by-three scalar matrix. -/
def scalarMatrixThree (b : Fin 3 → Fin 3 → R) : (Fin 3 → R) →ₗ[R] (Fin 3 → R) where
  toFun x j := ∑ r : Fin 3, b j r * x r
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext j
    change (∑ r : Fin 3, b j r * (a * x r)) = a * ∑ r : Fin 3, b j r * x r
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

lemma scalarMatrixThree_comp_apply (b c : Fin 3 → Fin 3 → R) (x : Fin 3 → R) (j : Fin 3) :
    scalarMatrixThree b (scalarMatrixThree c x) j =
      ∑ k : Fin 3, (∑ r : Fin 3, b j r * c r k) * x k := by
  change (∑ r : Fin 3, b j r * ∑ k : Fin 3, c r k * x k) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma cubicFourierOrthogonality (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3) :
    (∑ r : Fin 3, cubicCharacter t (j * r) * cubicCharacter t (-(k * r))) =
      if j = k then (3 : R) else 0 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  simp_rw [cubicCharacter_mul t hc]
  have hn1 : -(1 : Fin 3) = 2 := by decide
  have hn2 : -(2 : Fin 3) = 1 := by decide
  fin_cases j <;> fin_cases k
  all_goals norm_num [Fin.sum_univ_three, cubicCharacter, hn1, hn2]
  all_goals norm_num [Fin.val_neg', Fin.val_add, hn1, hn2]
  all_goals linear_combination ht

lemma cubicFourierOrthogonality_reverse (t : R) (ht : t ^ 2 + t + 1 = 0) (j k : Fin 3) :
    (∑ r : Fin 3, cubicCharacter t (-(j * r)) * cubicCharacter t (r * k)) =
      if j = k then (3 : R) else 0 := by
  calc
    _ = ∑ r : Fin 3, cubicCharacter t (k * r) * cubicCharacter t (-(j * r)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_comm r k, mul_comm]
    _ = if k = j then (3 : R) else 0 := cubicFourierOrthogonality t ht k j
    _ = _ := by simp only [eq_comm]

/-- Express original coordinates in the character basis. -/
def cubicFourierForward (t : R) : (Fin 3 → R) →ₗ[R] (Fin 3 → R) :=
  scalarMatrixThree (fun j r => cubicCharacter t (j * r))

variable [Invertible (3 : R)]

/-- Reconstruct original coordinates from the character coordinates. -/
def cubicFourierBackward (t : R) : (Fin 3 → R) →ₗ[R] (Fin 3 → R) :=
  (⅟(3 : R)) • scalarMatrixThree (fun j r => cubicCharacter t (-(j * r)))

lemma cubicFourierForward_backward (t : R) (ht : t ^ 2 + t + 1 = 0) (x : Fin 3 → R) :
    cubicFourierForward t (cubicFourierBackward t x) = x := by
  funext j
  change (∑ r : Fin 3, cubicCharacter t (j * r) *
    ((⅟(3 : R)) * ∑ k : Fin 3, cubicCharacter t (-(r * k)) * x k)) = x j
  calc
    _ = (⅟(3 : R)) * scalarMatrixThree (fun j r => cubicCharacter t (j * r))
        (scalarMatrixThree (fun r k => cubicCharacter t (-(r * k))) x) j := by
      change _ = (⅟(3 : R)) * ∑ r : Fin 3, cubicCharacter t (j * r) *
        ∑ k : Fin 3, cubicCharacter t (-(r * k)) * x k
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = (⅟(3 : R)) * ∑ k : Fin 3,
        (∑ r : Fin 3, cubicCharacter t (j * r) * cubicCharacter t (-(k * r))) * x k := by
      rw [scalarMatrixThree_comp_apply]
      simp only [mul_comm]
    _ = x j := by
      simp_rw [cubicFourierOrthogonality t ht]
      simp [← mul_assoc]

lemma cubicFourierBackward_forward (t : R) (ht : t ^ 2 + t + 1 = 0) (x : Fin 3 → R) :
    cubicFourierBackward t (cubicFourierForward t x) = x := by
  funext j
  change (⅟(3 : R)) * scalarMatrixThree (fun j r => cubicCharacter t (-(j * r)))
    (scalarMatrixThree (fun r k => cubicCharacter t (r * k)) x) j = x j
  rw [scalarMatrixThree_comp_apply]
  simp_rw [cubicFourierOrthogonality_reverse t ht]
  simp [← mul_assoc]

/-- The Fourier basis change is invertible over a ring containing a cubic root and 1/3. -/
def cubicFourierLinearEquiv (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (Fin 3 → R) ≃ₗ[R] (Fin 3 → R) where
  toLinearMap := cubicFourierForward t
  invFun := cubicFourierBackward t
  left_inv := cubicFourierBackward_forward t ht
  right_inv := cubicFourierForward_backward t ht

end SerrePositivity
