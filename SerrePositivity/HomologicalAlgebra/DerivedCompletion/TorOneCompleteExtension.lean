module

public import SerrePositivity.HomologicalAlgebra.QuotientTorOneConormal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConormalExtension
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleComparison

/-! # The first quotient Tor group supplies complete almost extension closure -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (I : Ideal R)

/-- Only scalar surjectivity on the actual first self-Tor of the quotient is
needed for extension closure. No condition on ordinary mod-aⁿ ideal images is assumed. -/
lemma completeIdealExtensionClosed_of_quotientTorOne_surjective
    (h : Function.Surjective (fun x : TorModule R 1 (R ⧸ I) (R ⧸ I) => a • x)) :
    CompleteIdealExtensionClosed R a I :=
  completeIdealExtensionClosed_of_conormal_surjective a I
    ((quotientTorOne_smul_surjective_iff_conormal R I a).mp h)

end SerrePositivity.DerivedCompletion
