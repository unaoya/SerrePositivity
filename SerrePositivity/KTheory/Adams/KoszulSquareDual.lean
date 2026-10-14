module

public import SerrePositivity.KTheory.Adams.KoszulPositiveEmbedding

/-! # Dual coordinates on the one-element Koszul square -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulSquareBottomDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f 0 ≫
    (mappingCone.snd (smulId a (oneKoszulComplex a))).v 0 0 (by omega) ≫
    (oneKoszulXZeroIso a).hom

abbrev oneKoszulSquareLeftDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f (-1) ≫
    (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-1) 0 (by omega) ≫
    (oneKoszulXZeroIso a).hom

abbrev oneKoszulSquareRightDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f (-1) ≫
    (mappingCone.snd (smulId a (oneKoszulComplex a))).v (-1) (-1) (by omega) ≫
    (oneKoszulXNegOneIso a).hom

abbrev oneKoszulSquareTopDual (a : R) :=
  (oneKoszulSquareConeIso a).hom.f (-2) ≫
    (mappingCone.fst (smulId a (oneKoszulComplex a))).1.v (-2) (-1) (by omega) ≫
    (oneKoszulXNegOneIso a).hom

@[reassoc (attr := simp)]
lemma oneKoszulSquareBottom_dual (a : R) :
    oneKoszulSquareBottom a ≫ oneKoszulSquareBottomDual a = 𝟙 _ := by
  rw [oneKoszulSquareBottom_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareLeft_dual (a : R) :
    oneKoszulSquareLeft a ≫ oneKoszulSquareLeftDual a = 𝟙 _ := by
  rw [oneKoszulSquareLeft_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareLeft_rightDual (a : R) :
    oneKoszulSquareLeft a ≫ oneKoszulSquareRightDual a = 0 := by
  rw [oneKoszulSquareLeft_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareRight_leftDual (a : R) :
    oneKoszulSquareRight a ≫ oneKoszulSquareLeftDual a = 0 := by
  rw [oneKoszulSquareRight_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareRight_dual (a : R) :
    oneKoszulSquareRight a ≫ oneKoszulSquareRightDual a = 𝟙 _ := by
  rw [oneKoszulSquareRight_cone_assoc]
  simp

@[reassoc (attr := simp)]
lemma oneKoszulSquareTop_dual (a : R) :
    oneKoszulSquareTop a ≫ oneKoszulSquareTopDual a = 𝟙 _ := by
  rw [oneKoszulSquareTop_cone_assoc]
  simp

lemma oneKoszulSquareBottomDual_bottom (a : R) :
    oneKoszulSquareBottomDual a ≫ oneKoszulSquareBottom a = 𝟙 _ := by
  apply oneKoszulSquareXZero_hom_ext a
  simp [Category.assoc]

lemma oneKoszulSquareMiddle_dual_decomposition (a : R) :
    oneKoszulSquareLeftDual a ≫ oneKoszulSquareLeft a +
      oneKoszulSquareRightDual a ≫ oneKoszulSquareRight a = 𝟙 _ := by
  apply oneKoszulSquareXNegOne_hom_ext a <;> simp [Category.assoc]

lemma oneKoszulSquareTopDual_top (a : R) :
    oneKoszulSquareTopDual a ≫ oneKoszulSquareTop a = 𝟙 _ := by
  apply oneKoszulSquareXNegTwo_hom_ext a
  simp [Category.assoc]

end Adams
end SerrePositivity
