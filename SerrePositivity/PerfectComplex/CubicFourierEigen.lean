module

public import SerrePositivity.PerfectComplex.CubicFourierTransform

/-! # Fourier columns diagonalize the right cyclic permutation -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- The right cyclic permutation of three coordinates. -/
def cubicVectorRotation : (Fin 3 → R) →ₗ[R] (Fin 3 → R) where
  toFun x j := x (j - 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma cubicFourierForward_zero (t : R) (x : Fin 3 → R) :
    cubicFourierForward t x 0 = ∑ r : Fin 3, x r := by
  simp [cubicFourierForward, scalarMatrixThree, cubicCharacter]

lemma cubicFourierForward_rotation (t : R) (ht : t ^ 2 + t + 1 = 0)
    (x : Fin 3 → R) (j : Fin 3) :
    cubicFourierForward t (cubicVectorRotation x) j =
      cubicCharacter t j * cubicFourierForward t x j := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hn1 : -(1 : Fin 3) = 2 := by decide
  have hn2 : -(2 : Fin 3) = 1 := by decide
  fin_cases j
  all_goals norm_num [cubicFourierForward, scalarMatrixThree, cubicVectorRotation,
    Fin.sum_univ_three, cubicCharacter, hn1, hn2]
  all_goals ring_nf
  all_goals try rw [hn1]
  all_goals try simp only [hc, ht4]
  all_goals ring

variable [Invertible (3 : R)]

lemma cubicFourierBackward_single (t : R) (j r : Fin 3) :
    cubicFourierBackward t (Pi.single j (1 : R)) r =
      (⅟(3 : R)) * cubicCharacter t (-(r * j)) := by
  simp [cubicFourierBackward, scalarMatrixThree, Pi.single_apply, mul_ite]

lemma cubicFourierBackward_sum (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3) :
    (∑ r : Fin 3, cubicFourierBackward t (Pi.single j (1 : R)) r) =
      if j = 0 then (1 : R) else 0 := by
  have he := congrArg (fun x : Fin 3 → R => x 0)
    (cubicFourierForward_backward t ht (Pi.single j (1 : R)))
  rw [cubicFourierForward_zero] at he
  simpa [Pi.single_apply, eq_comm] using he

lemma cubicFourierBackward_eigen (t : R) (ht : t ^ 2 + t + 1 = 0) (j : Fin 3) :
    cubicVectorRotation (cubicFourierBackward t (Pi.single j (1 : R))) =
      cubicCharacter t j • cubicFourierBackward t (Pi.single j (1 : R)) := by
  apply (cubicFourierLinearEquiv t ht).injective
  change cubicFourierForward t
      (cubicVectorRotation (cubicFourierBackward t (Pi.single j (1 : R)))) =
    cubicFourierForward t (cubicCharacter t j • cubicFourierBackward t (Pi.single j (1 : R)))
  rw [(cubicFourierForward t).map_smul, cubicFourierForward_backward t ht]
  funext r
  rw [cubicFourierForward_rotation t ht, cubicFourierForward_backward t ht]
  by_cases hr : r = j
  · subst r
    rfl
  · simp [hr]

end SerrePositivity
