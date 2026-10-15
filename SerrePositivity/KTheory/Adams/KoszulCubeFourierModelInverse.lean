module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierModelGenerators

/-! # Explicit degreewise inverses for the four-shift Fourier map -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

omit [Invertible (3 : R)] in
lemma oneKoszulCubeFourierModelX_hom_ext (a : R) (n : ℤ) {M : ModuleCat.{u} R}
    {f g : (oneKoszulCubeFourierModel a).X n ⟶ M}
    (h0 : (oneKoszulCubeFourierModelInZero a).f n ≫ f =
      (oneKoszulCubeFourierModelInZero a).f n ≫ g)
    (h1 : (oneKoszulCubeFourierModelInOne a).f n ≫ f =
      (oneKoszulCubeFourierModelInOne a).f n ≫ g)
    (h2 : (oneKoszulCubeFourierModelInTwo a).f n ≫ f =
      (oneKoszulCubeFourierModelInTwo a).f n ≫ g)
    (h3 : (oneKoszulCubeFourierModelInTop a).f n ≫ f =
      (oneKoszulCubeFourierModelInTop a).f n ≫ g) : f = g := by
  apply biprodX_ext_from h0
  apply biprodX_ext_from
  · simpa only [oneKoszulCubeFourierModelInOne, comp_f, Category.assoc] using h1
  · apply biprodX_ext_from
    · simpa only [oneKoszulCubeFourierModelInTwo, comp_f, Category.assoc] using h2
    · simpa only [oneKoszulCubeFourierModelInTop, comp_f, Category.assoc] using h3

def oneKoszulCubeFourierModelInverseZero (a _t : R) :
    (tensorCube (oneKoszulComplex a)).X (0) ⟶ (oneKoszulCubeFourierModel a).X (0) :=
  oneKoszulCubeBottomCoordinate a ≫
    (oneKoszulXZeroIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (0)

lemma oneKoszulCubeFourierModelInverseZero_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseZero a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (0) =
      𝟙 _ := by
  apply oneKoszulCubeXZero_hom_ext a
  all_goals simp only [oneKoszulCubeFourierModelInverseZero, Category.assoc]
  all_goals simp only [oneKoszulCubeFourierModelZeroUpper_map a t ht]
  all_goals simp

def oneKoszulCubeFourierModelInverseNegOne (a t : R) :
    (tensorCube (oneKoszulComplex a)).X (-1) ⟶ (oneKoszulCubeFourierModel a).X (-1) :=
  oneKoszulCubeFourierOneZeroCoordinate a ≫
      (oneKoszulXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (-1) +
    oneKoszulCubeFourierOneOneCoordinate a t ≫
      (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-1) +
    oneKoszulCubeFourierOneTwoCoordinate a t ≫
      (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-1)

lemma oneKoszulCubeFourierModelInverseNegOne_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseNegOne a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (-1) =
      𝟙 _ := by
  apply oneKoszulCubeFourierOne_hom_ext a t ht
  all_goals simp only [oneKoszulCubeFourierModelInverseNegOne, Category.assoc,
    comp_add, add_comp]
  all_goals simp only [oneKoszulCubeFourierModelZeroLower_map a t ht,
    oneKoszulCubeFourierModelOneUpper_map a t ht,
    oneKoszulCubeFourierModelTwoUpper_map a t ht]
  all_goals simp [ht]

def oneKoszulCubeFourierModelInverseNegTwo (a t : R) :
    (tensorCube (oneKoszulComplex a)).X (-2) ⟶ (oneKoszulCubeFourierModel a).X (-2) :=
  (-oneKoszulCubeFourierTwo01Coordinate a t) ≫
      (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-2) +
    (-oneKoszulCubeFourierTwo02Coordinate a t) ≫
      (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-2) +
    oneKoszulCubeFourierTwo12Coordinate a t ≫
      (oneKoszulShiftTwoXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-2)

lemma oneKoszulCubeFourierModelInverseNegTwo_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseNegTwo a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (-2) =
      𝟙 _ := by
  apply oneKoszulCubeFourierTwo_hom_ext a t ht
  all_goals simp only [oneKoszulCubeFourierModelInverseNegTwo, Category.assoc,
    comp_add, add_comp, neg_comp, comp_neg]
  all_goals simp only [oneKoszulCubeFourierModelOneLower_map a t ht,
    oneKoszulCubeFourierModelTwoLower_map a t ht,
    oneKoszulCubeFourierModelTopUpper_map a t ht]
  all_goals simp [ht]

def oneKoszulCubeFourierModelInverseNegThree (a t : R) :
    (tensorCube (oneKoszulComplex a)).X (-3) ⟶ (oneKoszulCubeFourierModel a).X (-3) :=
  oneKoszulCubeFourierTopCoordinate a t ≫
      (oneKoszulShiftTwoXNegThreeIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-3)

lemma oneKoszulCubeFourierModelInverseNegThree_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseNegThree a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (-3) =
      𝟙 _ := by
  apply oneKoszulCubeFourierTop_hom_ext a t ht
  all_goals simp only [oneKoszulCubeFourierModelInverseNegThree, Category.assoc]
  all_goals simp only [oneKoszulCubeFourierModelTopLower_map a t ht]
  all_goals simp [ht]

lemma oneKoszulCubeFourierModelMap_inverseZero (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (0) ≫ oneKoszulCubeFourierModelInverseZero a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (0)
  · apply (cancel_epi (oneKoszulXZeroIso a).inv).mp
    simp only [oneKoszulCubeFourierModelZeroUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseZero]
  · exact (oneKoszulShiftOne_isZero_X_other a (0) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftOne_isZero_X_other a (0) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftTwo_isZero_X_other a (0) (by omega)).eq_of_src _ _

lemma oneKoszulCubeFourierModelMap_inverseNegOne (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (-1) ≫ oneKoszulCubeFourierModelInverseNegOne a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (-1)
  · apply (cancel_epi (oneKoszulXNegOneIso a).inv).mp
    simp only [oneKoszulCubeFourierModelZeroLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegOne, comp_add, ht]
  · apply (cancel_epi (oneKoszulShiftOneXNegOneIso a).inv).mp
    simp only [oneKoszulCubeFourierModelOneUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegOne, comp_add, ht]
  · apply (cancel_epi (oneKoszulShiftOneXNegOneIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTwoUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegOne, comp_add, ht]
  · exact (oneKoszulShiftTwo_isZero_X_other a (-1) (by omega)).eq_of_src _ _

lemma oneKoszulCubeFourierModelMap_inverseNegTwo (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (-2) ≫ oneKoszulCubeFourierModelInverseNegTwo a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (-2)
  · exact (oneKoszul_isZero_X_other a (-2) (by omega)).eq_of_src _ _
  · apply (cancel_epi (oneKoszulShiftOneXNegTwoIso a).inv).mp
    simp only [oneKoszulCubeFourierModelOneLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegTwo, comp_add, neg_comp, comp_neg, ht]
  · apply (cancel_epi (oneKoszulShiftOneXNegTwoIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTwoLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegTwo, comp_add, neg_comp, comp_neg, ht]
  · apply (cancel_epi (oneKoszulShiftTwoXNegTwoIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTopUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegTwo, comp_add, neg_comp, comp_neg, ht]

lemma oneKoszulCubeFourierModelMap_inverseNegThree (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (-3) ≫ oneKoszulCubeFourierModelInverseNegThree a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (-3)
  · exact (oneKoszul_isZero_X_other a (-3) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftOne_isZero_X_other a (-3) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftOne_isZero_X_other a (-3) (by omega)).eq_of_src _ _
  · apply (cancel_epi (oneKoszulShiftTwoXNegThreeIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTopLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegThree, ht]

end Adams
end SerrePositivity
