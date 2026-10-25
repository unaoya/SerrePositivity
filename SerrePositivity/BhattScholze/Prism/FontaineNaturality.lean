module

public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality
public import SerrePositivity.CommutativeAlgebra.WittLiftUniqueness

/-! # BSの完全prism対応に使うFontaine写像の自然性

共通Witt持上げの一意性から導く。環のp正則性は要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
variable [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))]
variable [IsAdicComplete (Ideal.span {(p : R)}) R]
variable [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- 任意のp進完備環の射は、標準tilt射を介してFontaine写像と可換する。 -/
theorem fontaineTheta_natural (f : R →+* S) :
    (WittVector.fontaineTheta S p).comp
      (WittVector.map (Perfection.map p (modPMap p f))) =
      f.comp (WittVector.fontaineTheta R p) := by
  apply wittLift_unique
  apply RingHom.ext
  intro x
  change Ideal.Quotient.mk _ (WittVector.fontaineTheta S p
    (WittVector.map (Perfection.map p (modPMap p f)) x)) =
    Ideal.Quotient.mk _ (f (WittVector.fontaineTheta R p x))
  rw [WittVector.mk_fontaineTheta, WittVector.map_coeff]
  change modPMap p f (PreTilt.coeff 0 (x.coeff 0)) = _
  rw [← WittVector.mk_fontaineTheta]
  rfl

end SerrePositivity.BhattScholze
