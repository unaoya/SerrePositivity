module

public import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates

/-! # The twice-shifted one-element Koszul model and its positive differential sign -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulShiftTwo (a : R) := (oneKoszulComplex a)⟦(2 : ℤ)⟧

def oneKoszulShiftTwoXNegTwoIso (a : R) :
    (oneKoszulShiftTwo a).X (-2) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 2 (-2) 0 (by omega) ≪≫ oneKoszulXZeroIso a

def oneKoszulShiftTwoXNegThreeIso (a : R) :
    (oneKoszulShiftTwo a).X (-3) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 2 (-3) (-1) (by omega) ≪≫ oneKoszulXNegOneIso a

lemma oneKoszulShiftTwo_isZero_X_other (a : R) (n : ℤ) (hn : n ≠ -3 ∧ n ≠ -2) :
    IsZero ((oneKoszulShiftTwo a).X n) :=
  (oneKoszul_isZero_X_other a (n + 2) (by omega)).of_iso
    ((oneKoszulComplex a).shiftFunctorObjXIso 2 n (n + 2) rfl)

lemma oneKoszulShiftTwo_generator_d (a : R) :
    (oneKoszulShiftTwoXNegThreeIso a).inv ≫ (oneKoszulShiftTwo a).d (-3) (-2) =
      a • (oneKoszulShiftTwoXNegTwoIso a).inv := by
  change (oneKoszulXNegOneIso a).inv ≫
    ((2 : ℤ).negOnePow • (oneKoszulComplex a).d (-1) 0) = _
  rw [show (2 : ℤ).negOnePow = 1 from Int.negOnePow_two_mul 1, one_smul,
    oneKoszul_generator_d]
  rfl

end Adams
end SerrePositivity
