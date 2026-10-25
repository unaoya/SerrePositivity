module
public import SerrePositivity.CLMST.PerfectoidIdealRoots
public import SerrePositivity.BhattScholze.Semiperfectoid.SemiperfectoidSurjectivity
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidCompletedQuotientMul
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidRingEquiv
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComplete

/-! # The actual perfectoid ideal quotient and its original completed multiplication -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.CLMST
open CategoryTheory SerrePositivity.DerivedCompletion SerrePositivity.BhattScholze
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- The original selected perfectoidization of the principal quotient is surjective. -/
lemma perfectoidIdeal_quotientMap_surjective :
    Function.Surjective (toQuotientPerfectoidization R (Ideal.span {g}) p hR) :=
  surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR
    (Ideal.Quotient.mk (Ideal.span {g})) Ideal.Quotient.mk_surjective
    (isModuleComplete_principal_quotient_natCast R p g (hR.isModuleComplete R p))
    (toQuotientPerfectoidization R (Ideal.span {g}) p hR)
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR)

/-- The quotient by the original kernel ideal is the same selected perfectoid quotient. -/
lemma perfectoidIdeal_quotient_isIntegralPerfectoid :
    IsIntegralPerfectoid (R ⧸ perfectoidIdeal R p hR g) p := by
  let e := perfectoidIdealQuotientEquiv R p hR g
    (perfectoidIdeal_quotientMap_surjective R p hR g)
  exact isIntegralPerfectoid_of_ringEquiv p e.symm
    (isPerfectoidization_toQuotientPerfectoidization R (Ideal.span {g}) p hR).1

/-- The original completed quotient product for the actual CLMST perfectoid ideal is invertible. -/
lemma perfectoidIdeal_completedQuotientMul_isIso :
    IsIso ((derivedComplexCompletionFunctor R (p : R)).map
      (boundedAboveDerivedAlgebraMul (R := R) (R ⧸ perfectoidIdeal R p hR g)).hom) :=
  integralPerfectoid_completedQuotientMul_isIso p R (perfectoidIdeal R p hR g) hR
    (perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g)

/-- The complete almost-zero modules for the actual ideal are extension closed. -/
lemma perfectoidIdeal_completeIdealExtensionClosed :
    CompleteIdealExtensionClosed R (p : R) (perfectoidIdeal R p hR g) :=
  integralPerfectoid_completeIdealExtensionClosed p R (perfectoidIdeal R p hR g) hR
    (perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g)

/-- The original ideal has idempotent image in every p-power quotient, without a root choice. -/
lemma perfectoidIdeal_mod_power_idempotent (n : ℕ) :
    IsIdempotentElem ((perfectoidIdeal R p hR g).map
      (Ideal.Quotient.mk (Ideal.span {(p : R) ^ n}))) :=
  integralPerfectoid_ideal_mod_power_idempotent p R (perfectoidIdeal R p hR g) hR
    (perfectoidIdeal_quotient_isIntegralPerfectoid R p hR g) n

end SerrePositivity.CLMST
