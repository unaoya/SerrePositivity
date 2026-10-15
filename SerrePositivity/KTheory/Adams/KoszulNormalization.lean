module
public import SerrePositivity.PerfectComplex.KoszulClasses

public import SerrePositivity.KTheory.Adams.KoszulNegativeRetraction

/-! # One-element Koszul normalization for the cyclic Adams operation of degree two -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

lemma oneKoszulShiftOne_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (oneKoszulShiftOne a) (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
      (oneKoszulNegativeModel_support a)) = -oneKoszulClass a := by
  have hχ : ClosedSupportShortExactAdditive (oneKoszulSupport a)
      (K0WithSupport.mk (oneKoszulSupport a)) := K0WithSupport.mk_shortExact (oneKoszulSupport a)
  exact hχ.shift_one (fun e => K0WithSupport.mk_iso (oneKoszulSupport a) e)
    (oneKoszulComplex a) (oneKoszulComplex_perfect a) (oneKoszulComplex_support a)

variable [Invertible (2 : R)]

lemma oneKoszulPositive_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (tensorSquarePositive (oneKoszulComplex a))
      (tensorSquarePositive_perfect _ (oneKoszulComplex_perfect a))
      (tensorSquarePositive_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))) =
    oneKoszulClass a := by
  have he := K0WithSupport.mk_eq_of_quasiIso (oneKoszulSupport a)
    (tensorSquarePositive (oneKoszulComplex a)) (oneKoszulComplex (2 * a))
    (tensorSquarePositive_perfect _ (oneKoszulComplex_perfect a)) (oneKoszulComplex_perfect _)
    (tensorSquarePositive_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))
    (oneKoszulPositiveModel_support a) (oneKoszulPositiveIso a).inv
  exact he.trans (oneKoszulUnitMul_class a (unitOfInvertible (2 : R)))

lemma oneKoszulNegative_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (tensorSquareNegative (oneKoszulComplex a))
      (tensorSquareNegative_perfect _ (oneKoszulComplex_perfect a))
      (tensorSquareNegative_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))) =
    -oneKoszulClass a := by
  have he := K0WithSupport.mk_eq_of_quasiIso (oneKoszulSupport a)
    (tensorSquareNegative (oneKoszulComplex a)) (oneKoszulShiftOne a)
    (tensorSquareNegative_perfect _ (oneKoszulComplex_perfect a))
    (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
    (tensorSquareNegative_support (oneKoszulComplex_perfect a) (oneKoszulComplex_support a))
    (oneKoszulNegativeModel_support a) (oneKoszulNegativeIso a).inv
  exact he.trans (oneKoszulShiftOne_class a)

lemma tensorSquareClass_oneKoszul (a : R) :
    tensorSquareClass (oneKoszulComplex a) (oneKoszulSupport a)
      (oneKoszulComplex_perfect a) (oneKoszulComplex_support a) =
    (2 : ℤ) • oneKoszulClass a := by
  have he := congrArg₂ (fun x y : K0WithSupport (oneKoszulSupport a) => x - y)
    (oneKoszulPositive_class a) (oneKoszulNegative_class a)
  exact he.trans (by simp [sub_neg_eq_add, two_smul])

/-- Axiom A4, with no locality, regularity, or non-zero-divisor assumption. -/
lemma cyclicTwo_oneKoszul (a : R) :
    cyclicTwo (oneKoszulSupport a) (oneKoszulClass a) = (2 : ℤ) • oneKoszulClass a :=
  (cyclicTwo_mk_concrete (oneKoszulSupport a) (oneKoszulComplex a)
    (oneKoszulComplex_perfect a) (oneKoszulComplex_support a)).trans
      (tensorSquareClass_oneKoszul a)

end Adams
end SerrePositivity
