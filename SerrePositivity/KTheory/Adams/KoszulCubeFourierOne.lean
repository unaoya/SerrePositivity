module

public import SerrePositivity.KTheory.Adams.KoszulCubeDifferential
public import SerrePositivity.KTheory.Adams.KoszulCubeBasis
public import SerrePositivity.PerfectComplex.CubicFourierEigen

/-! # Degree minus one Fourier eigenvectors and their Koszul differentials -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

def oneKoszulCubeFourierOneZero (a : R) :=
  (⅟(3 : R)) • (oneKoszulCubeE0 a + oneKoszulCubeE1 a + oneKoszulCubeE2 a)

def oneKoszulCubeFourierOneOne (a t : R) :=
  (⅟(3 : R)) • (oneKoszulCubeE0 a + t ^ 2 • oneKoszulCubeE1 a + t • oneKoszulCubeE2 a)

def oneKoszulCubeFourierOneTwo (a t : R) :=
  (⅟(3 : R)) • (oneKoszulCubeE0 a + t • oneKoszulCubeE1 a + t ^ 2 • oneKoszulCubeE2 a)

lemma oneKoszulCubeFourierOneZero_rotation (a : R) :
    oneKoszulCubeFourierOneZero a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      oneKoszulCubeFourierOneZero a := by
  simp only [oneKoszulCubeFourierOneZero, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_rotation, oneKoszulCubeE1_rotation, oneKoszulCubeE2_rotation]
  module

lemma oneKoszulCubeFourierOneOne_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      t • oneKoszulCubeFourierOneOne a t := by
  have hp : t * t ^ 2 = 1 := by
    rw [← pow_succ', cube_eq_one_of_cubic_relation t ht]
  simp only [oneKoszulCubeFourierOneOne, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_rotation, oneKoszulCubeE1_rotation, oneKoszulCubeE2_rotation]
  rw [smul_comm t (⅟(3 : R))]
  congr 1
  simp only [smul_add, smul_smul, hp, one_smul, ← pow_two]
  module

lemma oneKoszulCubeFourierOneTwo_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      t ^ 2 • oneKoszulCubeFourierOneTwo a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hp : t ^ 2 * t = 1 := by rw [← pow_succ, hc]
  have hq : t ^ 2 * t ^ 2 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  simp only [oneKoszulCubeFourierOneTwo, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_rotation, oneKoszulCubeE1_rotation, oneKoszulCubeE2_rotation]
  rw [smul_comm (t ^ 2) (⅟(3 : R))]
  congr 1
  simp only [smul_add, smul_smul, hp, hq, one_smul]
  module

lemma oneKoszulCubeFourierOneZero_d (a : R) :
    oneKoszulCubeFourierOneZero a ≫ (tensorCube (oneKoszulComplex a)).d (-1) 0 =
      a • oneKoszulCubeBottom a := by
  simp only [oneKoszulCubeFourierOneZero, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_d, oneKoszulCubeE1_d, oneKoszulCubeE2_d]
  calc
    _ = (⅟(3 : R)) • ((3 : R) • (a • oneKoszulCubeBottom a)) := by module
    _ = _ := by rw [smul_smul, invOf_mul_self, one_smul]

lemma oneKoszulCubeFourierOneOne_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ (tensorCube (oneKoszulComplex a)).d (-1) 0 = 0 := by
  simp only [oneKoszulCubeFourierOneOne, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_d, oneKoszulCubeE1_d, oneKoszulCubeE2_d]
  calc
    _ = (⅟(3 : R)) • ((t ^ 2 + t + 1) • (a • oneKoszulCubeBottom a)) := by module
    _ = _ := by rw [ht, zero_smul, smul_zero]

lemma oneKoszulCubeFourierOneTwo_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ (tensorCube (oneKoszulComplex a)).d (-1) 0 = 0 := by
  simp only [oneKoszulCubeFourierOneTwo, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_d, oneKoszulCubeE1_d, oneKoszulCubeE2_d]
  calc
    _ = (⅟(3 : R)) • ((t ^ 2 + t + 1) • (a • oneKoszulCubeBottom a)) := by module
    _ = _ := by rw [ht, zero_smul, smul_zero]

end Adams
end SerrePositivity
