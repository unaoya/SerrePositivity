module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierOne

/-! # Reconstructing the degree minus one generators from the Fourier vectors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma oneKoszulCubeE0_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE0 a = oneKoszulCubeFourierOneZero a +
      oneKoszulCubeFourierOneOne a t + oneKoszulCubeFourierOneTwo a t := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  symm
  calc
    _ = (⅟(3 : R)) • ((3 : R) • oneKoszulCubeE0 a +
      (1 + t + t ^ 2) • oneKoszulCubeE1 a + (1 + t + t ^ 2) • oneKoszulCubeE2 a) := by
        unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwo
        module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, add_zero, smul_smul, invOf_mul_self, one_smul]

lemma oneKoszulCubeE1_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE1 a = oneKoszulCubeFourierOneZero a +
      t • oneKoszulCubeFourierOneOne a t + t ^ 2 • oneKoszulCubeFourierOneTwo a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  have hs' : 1 + t ^ 2 + t = 0 := by linear_combination ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  symm
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • oneKoszulCubeE0 a +
      (1 + t ^ 3 + t ^ 3) • oneKoszulCubeE1 a +
      (1 + t ^ 2 + t ^ 4) • oneKoszulCubeE2 a) := by
        unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwo
        module
    _ = _ := by
      rw [hc, ht4, hs, hs']
      simp only [zero_smul, zero_add, add_zero, show (1 + 1 + 1 : R) = 3 from by norm_num,
        smul_smul, invOf_mul_self, one_smul]

lemma oneKoszulCubeE2_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE2 a = oneKoszulCubeFourierOneZero a +
      t ^ 2 • oneKoszulCubeFourierOneOne a t + t • oneKoszulCubeFourierOneTwo a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  have hs' : 1 + t ^ 2 + t = 0 := by linear_combination ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  symm
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • oneKoszulCubeE0 a +
      (1 + t ^ 2 + t ^ 4) • oneKoszulCubeE1 a +
      (1 + t ^ 3 + t ^ 3) • oneKoszulCubeE2 a) := by
        unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwo
        module
    _ = _ := by
      rw [hc, ht4, hs, hs']
      simp only [zero_smul, zero_add, add_zero, show (1 + 1 + 1 : R) = 3 from by norm_num,
        smul_smul, invOf_mul_self, one_smul]

end Adams
end SerrePositivity
