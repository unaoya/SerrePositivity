module

public import SerrePositivity.KTheory.Adams.KoszulPositiveRetraction

/-! # The shifted one-element Koszul model and its differential sign -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulShiftOne (a : R) := (oneKoszulComplex a)⟦(1 : ℤ)⟧

def oneKoszulShiftOneXNegOneIso (a : R) :
    (oneKoszulShiftOne a).X (-1) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 1 (-1) 0 (by omega) ≪≫ oneKoszulXZeroIso a

def oneKoszulShiftOneXNegTwoIso (a : R) :
    (oneKoszulShiftOne a).X (-2) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 1 (-2) (-1) (by omega) ≪≫ oneKoszulXNegOneIso a

lemma oneKoszulShiftOne_isZero_X_other (a : R) (n : ℤ) (hn : n ≠ -2 ∧ n ≠ -1) :
    IsZero ((oneKoszulShiftOne a).X n) :=
  (oneKoszul_isZero_X_other a (n + 1) (by omega)).of_iso
    ((oneKoszulComplex a).shiftFunctorObjXIso 1 n (n + 1) rfl)

lemma oneKoszulShiftOne_generator_d (a : R) :
    (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulShiftOne a).d (-2) (-1) =
      -(a • (oneKoszulShiftOneXNegOneIso a).inv) := by
  change (oneKoszulXNegOneIso a).inv ≫
    ((1 : ℤ).negOnePow • (oneKoszulComplex a).d (-1) 0) = _
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.comp_neg]
  rw [oneKoszul_generator_d]
  rfl

abbrev oneKoszulSquareNegativeGenerator (a : R) :=
  oneKoszulSquareLeft a - oneKoszulSquareRight a

lemma oneKoszulSquareNegativeGenerator_d (a : R) :
    oneKoszulSquareNegativeGenerator a ≫ (tensorSquare (oneKoszulComplex a)).d (-1) 0 = 0 := by
  rw [Preadditive.sub_comp, oneKoszulSquareLeft_d, oneKoszulSquareRight_d, sub_self]

lemma oneKoszulSquareTop_d_negative (a : R) :
    oneKoszulSquareTop a ≫ (tensorSquare (oneKoszulComplex a)).d (-2) (-1) =
      -(a • oneKoszulSquareNegativeGenerator a) := by
  rw [oneKoszulSquareTop_d]
  simp [oneKoszulSquareNegativeGenerator, smul_sub, neg_sub]

end Adams
end SerrePositivity
