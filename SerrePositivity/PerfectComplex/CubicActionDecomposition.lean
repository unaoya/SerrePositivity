module

public import SerrePositivity.PerfectComplex.CubicActionProjector
public import SerrePositivity.CommutativeAlgebra.CubicCyclotomicAlgebra
public import Mathlib.Tactic.Module

/-! # Three orthogonal character projectors for a cubic chain action -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

/-- The three character values, with indices taken modulo three. -/
def cubicCharacter (t : R) (j : Fin 3) : R := t ^ (j : ℕ)

lemma cubicCharacter_cube (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    cubicCharacter t j ^ 3 = 1 := by
  rw [cubicCharacter, ← pow_mul, mul_comm, pow_mul, ht, one_pow]

lemma cubicCharacter_mul (t : R) (ht : t ^ 3 = 1) (i j : Fin 3) :
    cubicCharacter t i * cubicCharacter t j = cubicCharacter t (i + j) := by
  change t ^ (i : ℕ) * t ^ (j : ℕ) = t ^ ((i + j : Fin 3) : ℕ)
  rw [Fin.val_add, ← pow_add]
  calc
    t ^ ((i : ℕ) + (j : ℕ)) =
        t ^ (((i : ℕ) + (j : ℕ)) % 3 + 3 * (((i : ℕ) + (j : ℕ)) / 3)) :=
      congrArg (fun n : ℕ => t ^ n) (Nat.mod_add_div _ 3).symm
    _ = _ := by rw [pow_add, pow_mul, ht, one_pow, mul_one]

lemma sum_cubicCharacter (t : R) (ht : t ^ 2 + t + 1 = 0) :
    ∑ j : Fin 3, cubicCharacter t j = 0 := by
  rw [Fin.sum_univ_three]
  simp only [cubicCharacter, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  calc
    1 + t + t ^ 2 = t ^ 2 + t + 1 := by ring
    _ = 0 := ht

lemma cubicCharacter_difference_isUnit [Invertible (3 : R)] (t : R)
    (ht : t ^ 2 + t + 1 = 0) (i j : Fin 3) (hne : i ≠ j) :
    IsUnit (cubicCharacter t i - cubicCharacter t j) := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hu : IsUnit t := by
    let : Invertible t := invertibleOfPowEqOne t 3 hc (by decide)
    exact isUnit_of_invertible t
  obtain ⟨h01, h02⟩ := isUnit_one_sub_of_cubic_relation t ht (isUnit_of_invertible (3 : R))
  have h10 : IsUnit (t - 1) := by simpa only [neg_sub] using h01.neg
  have h20 : IsUnit (t ^ 2 - 1) := by simpa only [neg_sub] using h02.neg
  have h12 : IsUnit (t - t ^ 2) := by
    convert hu.mul h01 using 1
    ring
  have h21 : IsUnit (t ^ 2 - t) := by simpa only [neg_sub] using h12.neg
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hne rfl).elim
    | simp only [cubicCharacter, pow_zero, pow_one]
      first | exact h01 | exact h02 | exact h10 | exact h20 | exact h12 | exact h21

namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

lemma sum_character_projectorMap (τ : CochainCubicAction K) (t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    ∑ j : Fin 3, τ.projectorMap (cubicCharacter t j) = 𝟙 K := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hs : 1 + t + t ^ 2 = 0 := by
    calc
      _ = t ^ 2 + t + 1 := by ring
      _ = 0 := ht
  rw [Fin.sum_univ_three]
  simp only [cubicCharacter, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  calc
    τ.projectorMap 1 + τ.projectorMap t + τ.projectorMap (t ^ 2) =
        (⅟(3 : R)) • ((3 : R) • (𝟙 K : K ⟶ K) +
          (1 + t ^ 2 + t ^ 4) • τ.map + (1 + t + t ^ 2) • (τ.map ≫ τ.map)) := by
      simp only [projectorMap]
      module
    _ = 𝟙 K := by
      have hs' : 1 + t ^ 2 + t = 0 := by simpa only [add_right_comm] using hs
      rw [ht4, hs', hs, zero_smul, zero_smul, add_zero, add_zero,
        smul_smul, invOf_mul_self, one_smul]

/-- The three eigenspace idempotents. -/
def characterProjector (τ : CochainCubicAction K) (t : R) (ht : t ^ 3 = 1)
    (j : Fin 3) : CochainIdempotent K :=
  τ.projector (cubicCharacter t j) (cubicCharacter_cube t ht j)

lemma characterProjector_orthogonal (τ : CochainCubicAction K) (t : R)
    (ht : t ^ 2 + t + 1 = 0) (i j : Fin 3) (hne : i ≠ j) :
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i).map ≫
      (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).map = 0 :=
  τ.projectorMap_orthogonal _ _ (cubicCharacter_cube _ (cube_eq_one_of_cubic_relation t ht) i)
    (cubicCharacter_cube _ (cube_eq_one_of_cubic_relation t ht) j)
    (cubicCharacter_difference_isUnit t ht i j hne)

/-- The original complex is the finite biproduct of its three character parts. -/
def characterDecompositionIso (τ : CochainCubicAction K) (t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    (⨁ fun j : Fin 3 =>
      (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image) ≅ K :=
  CochainIdempotent.decompositionIso _ (τ.characterProjector_orthogonal t ht)
    (τ.sum_character_projectorMap t ht)

end CochainCubicAction
end SerrePositivity
