module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierOneInverse

/-! # Coordinates dual to the three degree minus one Fourier vectors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

def oneKoszulCubeFourierOneZeroCoordinate (a : R) :=
  oneKoszulCubeE0Coordinate a + oneKoszulCubeE1Coordinate a + oneKoszulCubeE2Coordinate a

def oneKoszulCubeFourierOneOneCoordinate (a t : R) :=
  oneKoszulCubeE0Coordinate a + t • oneKoszulCubeE1Coordinate a + t ^ 2 •
    oneKoszulCubeE2Coordinate a

def oneKoszulCubeFourierOneTwoCoordinate (a t : R) :=
  oneKoszulCubeE0Coordinate a + t ^ 2 • oneKoszulCubeE1Coordinate a + t •
    oneKoszulCubeE2Coordinate a

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneZero_ZeroCoordinate (a : R) :
    oneKoszulCubeFourierOneZero a ≫ oneKoszulCubeFourierOneZeroCoordinate a = 𝟙 _ := by
  calc
    _ = (⅟(3 : R)) • ((3 : R) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneZeroCoordinate
      simp only [Linear.smul_comp, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [smul_smul, invOf_mul_self, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneZero_OneCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneZero a ≫ oneKoszulCubeFourierOneOneCoordinate a t = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOneCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneZero_TwoCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneZero a ≫ oneKoszulCubeFourierOneTwoCoordinate a t = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneTwoCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneOne_ZeroCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ oneKoszulCubeFourierOneZeroCoordinate a = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneZeroCoordinate
      simp only [Linear.smul_comp, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneOne_OneCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ oneKoszulCubeFourierOneOneCoordinate a t = 𝟙 _ := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t ^ 3 + t ^ 3 = (3 : R) := by rw [hc]; norm_num
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 3 + t ^ 3) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneOneCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      rw [smul_smul, invOf_mul_self, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneOne_TwoCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ oneKoszulCubeFourierOneTwoCoordinate a t = 0 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hs : 1 + t ^ 2 + t ^ 4 = 0 := by linear_combination ht + ht4
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 2 + t ^ 4) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwoCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneTwo_ZeroCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ oneKoszulCubeFourierOneZeroCoordinate a = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneTwo oneKoszulCubeFourierOneZeroCoordinate
      simp only [Linear.smul_comp, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneTwo_OneCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ oneKoszulCubeFourierOneOneCoordinate a t = 0 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hs : 1 + t ^ 2 + t ^ 4 = 0 := by linear_combination ht + ht4
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 2 + t ^ 4) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneTwo oneKoszulCubeFourierOneOneCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneTwo_TwoCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ oneKoszulCubeFourierOneTwoCoordinate a t = 𝟙 _ := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t ^ 3 + t ^ 3 = (3 : R) := by rw [hc]; norm_num
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 3 + t ^ 3) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneTwo oneKoszulCubeFourierOneTwoCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      rw [smul_smul, invOf_mul_self, one_smul]

end Adams
end SerrePositivity
