module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierOneInverse

/-! # Fourier minors in degree minus two and the determinant in degree minus three -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

/-- The minor column corresponding to v₀ wedge v₁. -/
def oneKoszulCubeFourierTwo01 (a t : R) :=
  (⅟(3 : R)) ^ 2 • ((t ^ 2 - 1) • oneKoszulCubeE01 a +
    (t - 1) • oneKoszulCubeE02 a + (t - t ^ 2) • oneKoszulCubeE12 a)

/-- The minor column corresponding to v₀ wedge v₂. -/
def oneKoszulCubeFourierTwo02 (a t : R) :=
  (⅟(3 : R)) ^ 2 • ((t - 1) • oneKoszulCubeE01 a +
    (t ^ 2 - 1) • oneKoszulCubeE02 a + (t ^ 2 - t) • oneKoszulCubeE12 a)

/-- The minor column corresponding to v₁ wedge v₂. -/
def oneKoszulCubeFourierTwo12 (a t : R) :=
  ((⅟(3 : R)) ^ 2 * (t - t ^ 2)) •
    (oneKoszulCubeE01 a - oneKoszulCubeE02 a + oneKoszulCubeE12 a)

/-- The determinant column corresponding to v₀ wedge v₁ wedge v₂. -/
def oneKoszulCubeFourierTop (a t : R) :=
  ((⅟(3 : R)) ^ 2 * (t - t ^ 2)) • oneKoszulCubeTop a

lemma oneKoszulCubeFourierTwo01_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo01 a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      t • oneKoszulCubeFourierTwo01 a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have h0 : t * (t ^ 2 - 1) = 1 - t := by linear_combination hc
  have h1 : t * (t - 1) = t ^ 2 - t := by ring
  have h2 : t * (t - t ^ 2) = t ^ 2 - 1 := by linear_combination -hc
  simp only [oneKoszulCubeFourierTwo01, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_rotation, oneKoszulCubeE02_rotation, oneKoszulCubeE12_rotation]
  rw [smul_comm t ((⅟(3 : R)) ^ 2)]
  congr 1
  simp only [smul_add, smul_smul, h0, h1, h2]
  module

lemma oneKoszulCubeFourierTwo02_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo02 a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      t ^ 2 • oneKoszulCubeFourierTwo02 a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have h0 : t ^ 2 * (t - 1) = 1 - t ^ 2 := by linear_combination hc
  have h1 : t ^ 2 * (t ^ 2 - 1) = t - t ^ 2 := by linear_combination ht4
  have h2 : t ^ 2 * (t ^ 2 - t) = t - 1 := by linear_combination ht4 - hc
  simp only [oneKoszulCubeFourierTwo02, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_rotation, oneKoszulCubeE02_rotation, oneKoszulCubeE12_rotation]
  rw [smul_comm (t ^ 2) ((⅟(3 : R)) ^ 2)]
  congr 1
  simp only [smul_add, smul_smul, h0, h1, h2]
  module

lemma oneKoszulCubeFourierTwo12_rotation (a t : R) :
    oneKoszulCubeFourierTwo12 a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      oneKoszulCubeFourierTwo12 a t := by
  simp only [oneKoszulCubeFourierTwo12, Linear.smul_comp, add_comp, sub_comp,
    oneKoszulCubeE01_rotation, oneKoszulCubeE02_rotation, oneKoszulCubeE12_rotation]
  module

lemma oneKoszulCubeFourierTop_rotation (a t : R) :
    oneKoszulCubeFourierTop a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-3) =
      oneKoszulCubeFourierTop a t := by
  simp only [oneKoszulCubeFourierTop, Linear.smul_comp, oneKoszulCubeTop_rotation]

lemma oneKoszulCubeFourierTwo01_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo01 a t ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulCubeFourierOneOne a t := by
  have h0 : 2 - t - t ^ 2 = 3 := by linear_combination -ht
  have h1 : 2 * t ^ 2 - t - 1 = 3 * t ^ 2 := by linear_combination -ht
  have h2 : 2 * t - t ^ 2 - 1 = 3 * t := by linear_combination -ht
  have hi : (⅟(3 : R)) ^ 2 * 3 = ⅟(3 : R) := by
    rw [pow_two, mul_assoc, invOf_mul_self, mul_one]
  simp only [oneKoszulCubeFourierTwo01, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_d, oneKoszulCubeE02_d, oneKoszulCubeE12_d]
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 - t - t ^ 2) • (a • oneKoszulCubeE0 a) +
      (2 * t ^ 2 - t - 1) • (a • oneKoszulCubeE1 a) +
      (2 * t - t ^ 2 - 1) • (a • oneKoszulCubeE2 a)) := by module
    _ = (⅟(3 : R)) ^ 2 • ((3 : R) •
      (a • (oneKoszulCubeE0 a + t ^ 2 • oneKoszulCubeE1 a + t • oneKoszulCubeE2 a))) := by
        rw [h0, h1, h2]
        module
    _ = _ := by
      rw [smul_smul, hi]
      unfold oneKoszulCubeFourierOneOne
      module

lemma oneKoszulCubeFourierTwo02_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo02 a t ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulCubeFourierOneTwo a t := by
  have h0 : 2 - t - t ^ 2 = 3 := by linear_combination -ht
  have h1 : 2 * t - t ^ 2 - 1 = 3 * t := by linear_combination -ht
  have h2 : 2 * t ^ 2 - t - 1 = 3 * t ^ 2 := by linear_combination -ht
  have hi : (⅟(3 : R)) ^ 2 * 3 = ⅟(3 : R) := by
    rw [pow_two, mul_assoc, invOf_mul_self, mul_one]
  simp only [oneKoszulCubeFourierTwo02, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_d, oneKoszulCubeE02_d, oneKoszulCubeE12_d]
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 - t - t ^ 2) • (a • oneKoszulCubeE0 a) +
      (2 * t - t ^ 2 - 1) • (a • oneKoszulCubeE1 a) +
      (2 * t ^ 2 - t - 1) • (a • oneKoszulCubeE2 a)) := by module
    _ = (⅟(3 : R)) ^ 2 • ((3 : R) •
      (a • (oneKoszulCubeE0 a + t • oneKoszulCubeE1 a + t ^ 2 • oneKoszulCubeE2 a))) := by
        rw [h0, h1, h2]
        module
    _ = _ := by
      rw [smul_smul, hi]
      unfold oneKoszulCubeFourierOneTwo
      module

lemma oneKoszulCubeFourierTwo12_d (a t : R) :
    oneKoszulCubeFourierTwo12 a t ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) = 0 := by
  simp only [oneKoszulCubeFourierTwo12, Linear.smul_comp, add_comp, sub_comp,
    oneKoszulCubeE01_d, oneKoszulCubeE02_d, oneKoszulCubeE12_d]
  module

lemma oneKoszulCubeFourierTop_d (a t : R) :
    oneKoszulCubeFourierTop a t ≫ (tensorCube (oneKoszulComplex a)).d (-3) (-2) =
      a • oneKoszulCubeFourierTwo12 a t := by
  simp only [oneKoszulCubeFourierTop, oneKoszulCubeFourierTwo12, Linear.smul_comp,
    oneKoszulCubeTop_d]
  module

end Adams
end SerrePositivity
