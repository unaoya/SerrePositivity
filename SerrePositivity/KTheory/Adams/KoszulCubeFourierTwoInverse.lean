module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierTwo
public import SerrePositivity.PerfectComplex.CubicFourierMinorIdentities

/-! # Inverse Fourier minor and determinant formulas on Koszul cube generators -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma oneKoszulCubeE01_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE01 a = (t - 1) • oneKoszulCubeFourierTwo01 a t +
      (t ^ 2 - 1) • oneKoszulCubeFourierTwo02 a t -
      (t - t ^ 2) • oneKoszulCubeFourierTwo12 a t := by
  have hd : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  have hz : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 •
      ((2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2) • oneKoszulCubeE01 a +
      ((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2) • oneKoszulCubeE02 a) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12
        module
    _ = _ := by
      rw [hd, hz]
      simp only [zero_smul, add_zero, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

lemma oneKoszulCubeE02_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE02 a = (t ^ 2 - 1) • oneKoszulCubeFourierTwo01 a t +
      (t - 1) • oneKoszulCubeFourierTwo02 a t +
      (t - t ^ 2) • oneKoszulCubeFourierTwo12 a t := by
  have hd : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  have hz : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 •
      (((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2) • oneKoszulCubeE01 a +
      (2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2) • oneKoszulCubeE02 a) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12
        module
    _ = _ := by
      rw [hd, hz]
      simp only [zero_smul, zero_add, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

lemma oneKoszulCubeE12_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE12 a = -(t - t ^ 2) •
      (oneKoszulCubeFourierTwo01 a t - oneKoszulCubeFourierTwo02 a t +
        oneKoszulCubeFourierTwo12 a t) := by
  have hd : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2) • oneKoszulCubeE12 a) := by
      unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12
      module
    _ = _ := by
      rw [hd, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

lemma oneKoszulCubeTop_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeTop a = (3 * (t ^ 2 - t)) • oneKoszulCubeFourierTop a t := by
  have hd : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2) • oneKoszulCubeTop a) := by
      unfold oneKoszulCubeFourierTop
      module
    _ = _ := by
      rw [hd, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

end Adams
end SerrePositivity
