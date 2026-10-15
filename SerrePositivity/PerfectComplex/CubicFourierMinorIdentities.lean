module

public import SerrePositivity.PerfectComplex.CubicFourierTransform

/-! # Scalar identities for the Fourier minors and determinant -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

lemma cubicFourierMinor_pair_product (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (t ^ 2 - 1) * (t - 1) = 3 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  linear_combination hc - ht

lemma cubicFourierMinor_difference_square (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (t - t ^ 2) ^ 2 = -3 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  linear_combination ht - 2 * hc + ht4

lemma cubicFourierMinor_pair_square_sum (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 = 3 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  linear_combination ht4 - ht

lemma cubicFourierMinor_difference_product (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (t - t ^ 2) * (t ^ 2 - t) = 3 := by
  linear_combination -cubicFourierMinor_difference_square t ht

variable [Invertible (3 : R)]

lemma cubicFourierMinor_inverse_three_squared : (⅟(3 : R)) ^ 2 * 9 = 1 := by
  calc
    _ = ((⅟(3 : R)) * 3) ^ 2 := by ring
    _ = 1 := by rw [invOf_mul_self, one_pow]

lemma cubicFourierDeterminant_normalized (t : R) (ht : t ^ 2 + t + 1 = 0) :
    (⅟(3 : R)) ^ 3 * (t ^ 4 - 3 * t ^ 2 + 2 * t) =
      (⅟(3 : R)) ^ 2 * (t - t ^ 2) := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hi : (⅟(3 : R)) ^ 3 * 3 = (⅟(3 : R)) ^ 2 := by
    rw [pow_succ, mul_assoc, invOf_mul_self, mul_one]
  calc
    _ = ((⅟(3 : R)) ^ 3 * 3) * (t - t ^ 2) := by rw [ht4]; ring
    _ = _ := by rw [hi]

end SerrePositivity
