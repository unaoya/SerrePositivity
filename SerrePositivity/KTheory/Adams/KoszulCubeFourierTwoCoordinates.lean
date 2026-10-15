module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierTwoInverse

/-! # Dual coordinates for the degree minus two Fourier minors and the top determinant -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

def oneKoszulCubeFourierTwo01Coordinate (a t : R) :=
  (t - 1) • oneKoszulCubeE01Coordinate a + (t ^ 2 - 1) • oneKoszulCubeE02Coordinate a -
    (t - t ^ 2) • oneKoszulCubeE12Coordinate a

def oneKoszulCubeFourierTwo02Coordinate (a t : R) :=
  (t ^ 2 - 1) • oneKoszulCubeE01Coordinate a + (t - 1) • oneKoszulCubeE02Coordinate a +
    (t - t ^ 2) • oneKoszulCubeE12Coordinate a

def oneKoszulCubeFourierTwo12Coordinate (a t : R) :=
  -(t - t ^ 2) • (oneKoszulCubeE01Coordinate a - oneKoszulCubeE02Coordinate a +
    oneKoszulCubeE12Coordinate a)

def oneKoszulCubeFourierTopCoordinate (a t : R) :=
  (3 * (t ^ 2 - t)) • oneKoszulCubeTopCoordinate a

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo01_Two01Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo01 a t ≫ oneKoszulCubeFourierTwo01Coordinate a t = 𝟙 _ := by
  have hs : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo01Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      rw [smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo01_Two02Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo01 a t ≫ oneKoszulCubeFourierTwo02Coordinate a t = 0 := by
  have hs : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • (((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo01_Two12Coordinate (a t : R)
    : oneKoszulCubeFourierTwo01 a t ≫ oneKoszulCubeFourierTwo12Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo12Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo02_Two01Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo02 a t ≫ oneKoszulCubeFourierTwo01Coordinate a t = 0 := by
  have hs : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • (((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo01Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo02_Two02Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo02 a t ≫ oneKoszulCubeFourierTwo02Coordinate a t = 𝟙 _ := by
  have hs : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo02Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      rw [smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo02_Two12Coordinate (a t : R)
    : oneKoszulCubeFourierTwo02 a t ≫ oneKoszulCubeFourierTwo12Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo12_Two01Coordinate (a t : R)
    : oneKoszulCubeFourierTwo12 a t ≫ oneKoszulCubeFourierTwo01Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo12 oneKoszulCubeFourierTwo01Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, sub_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo12_Two02Coordinate (a t : R)
    : oneKoszulCubeFourierTwo12 a t ≫ oneKoszulCubeFourierTwo02Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo12 oneKoszulCubeFourierTwo02Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, sub_comp, comp_add,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo12_Two12Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo12 a t ≫ oneKoszulCubeFourierTwo12Coordinate a t = 𝟙 _ := by
  have hs : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo12 oneKoszulCubeFourierTwo12Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, sub_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      rw [smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTop_TopCoordinate (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTop a t ≫ oneKoszulCubeFourierTopCoordinate a t = 𝟙 _ := by
  have hs : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTop oneKoszulCubeFourierTopCoordinate
        simp only [Linear.smul_comp, Linear.comp_smul, oneKoszulCubeTop_TopCoordinate]
        module
    _ = _ := by rw [hs, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

end Adams
end SerrePositivity
