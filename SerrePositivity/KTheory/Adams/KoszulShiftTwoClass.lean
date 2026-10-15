module

public import SerrePositivity.KTheory.Adams.KoszulNormalization
public import SerrePositivity.KTheory.Adams.KoszulShiftTwoModel

/-! # The closed-support class of a twice-shifted one-element Koszul complex -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

lemma oneKoszulShiftTwo_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (oneKoszulShiftTwo a) (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 2)
      ((oneKoszulComplex_support a).shift 2)) = oneKoszulClass a := by
  let hp := strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1
  let hs := (oneKoszulComplex_support a).shift 1
  have hχ : ClosedSupportShortExactAdditive (oneKoszulSupport a)
      (K0WithSupport.mk (oneKoszulSupport a)) := K0WithSupport.mk_shortExact (oneKoszulSupport a)
  have h2 := hχ.shift_one (fun e => K0WithSupport.mk_iso (oneKoszulSupport a) e)
    (oneKoszulShiftOne a) hp hs
  have he := K0WithSupport.mk_eq_of_quasiIso (oneKoszulSupport a)
    (oneKoszulShiftTwo a) ((oneKoszulShiftOne a)⟦(1 : ℤ)⟧)
    (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 2)
    (strictlyPerfectComplex_shift hp 1) ((oneKoszulComplex_support a).shift 2) (hs.shift 1)
    ((shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ)
      (1 : ℤ) 1 2 (by norm_num)).app (oneKoszulComplex a)).hom
  rw [he, h2, oneKoszulShiftOne_class a, neg_neg]

end Adams
end SerrePositivity
