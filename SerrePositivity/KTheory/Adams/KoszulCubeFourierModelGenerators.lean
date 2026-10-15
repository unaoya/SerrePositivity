module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourierModelMap

/-! # Homogeneous generators of the four-shift Fourier model -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulCubeFourierModelTail (a : R) :=
  oneKoszulShiftOne a ⊞ (oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a)

abbrev oneKoszulCubeFourierModelInZero (a : R) :
    oneKoszulComplex a ⟶ oneKoszulCubeFourierModel a := biprod.inl

abbrev oneKoszulCubeFourierModelInOne (a : R) :
    oneKoszulShiftOne a ⟶ oneKoszulCubeFourierModel a :=
  (biprod.inl : oneKoszulShiftOne a ⟶ oneKoszulCubeFourierModelTail a) ≫ biprod.inr

abbrev oneKoszulCubeFourierModelInTwo (a : R) :
    oneKoszulShiftOne a ⟶ oneKoszulCubeFourierModel a :=
  (biprod.inl : oneKoszulShiftOne a ⟶ oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a) ≫
    (biprod.inr : _ ⟶ oneKoszulCubeFourierModelTail a) ≫ biprod.inr

abbrev oneKoszulCubeFourierModelInTop (a : R) :
    oneKoszulShiftTwo a ⟶ oneKoszulCubeFourierModel a :=
  (biprod.inr : oneKoszulShiftTwo a ⟶ oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a) ≫
    (biprod.inr : _ ⟶ oneKoszulCubeFourierModelTail a) ≫ biprod.inr

variable [Invertible (3 : R)]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInZero_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInZero a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierZeroEmbedding a := by
  simp [oneKoszulCubeFourierModelMap]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInOne_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInOne a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierOneEmbedding a t ht := by
  simp [oneKoszulCubeFourierModelMap, Category.assoc]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInTwo_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInTwo a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierTwoEmbedding a t ht := by
  simp [oneKoszulCubeFourierModelMap, Category.assoc]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInTop_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInTop a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierTopEmbedding a t := by
  simp [oneKoszulCubeFourierModelMap, Category.assoc]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelZeroLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (-1) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-1) = oneKoszulCubeFourierOneZero a := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInZero_map]
  simp [oneKoszulCubeFourierZeroEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelZeroUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulXZeroIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (0) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (0) = oneKoszulCubeBottom a := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInZero_map]
  simp [oneKoszulCubeFourierZeroEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelOneLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-2) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-2) = -oneKoszulCubeFourierTwo01 a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInOne_map]
  simp [oneKoszulCubeFourierOneEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelOneUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-1) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-1) = oneKoszulCubeFourierOneOne a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInOne_map]
  simp [oneKoszulCubeFourierOneEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTwoLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-2) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-2) = -oneKoszulCubeFourierTwo02 a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTwo_map]
  simp [oneKoszulCubeFourierTwoEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTwoUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-1) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-1) = oneKoszulCubeFourierOneTwo a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTwo_map]
  simp [oneKoszulCubeFourierTwoEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTopLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftTwoXNegThreeIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-3) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-3) = oneKoszulCubeFourierTop a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTop_map]
  simp [oneKoszulCubeFourierTopEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTopUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftTwoXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-2) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-2) = oneKoszulCubeFourierTwo12 a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTop_map]
  simp [oneKoszulCubeFourierTopEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

end Adams
end SerrePositivity
