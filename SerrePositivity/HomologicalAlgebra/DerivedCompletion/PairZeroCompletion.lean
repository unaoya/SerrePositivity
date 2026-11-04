module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion

/-! # A zero second coordinate preserves the original principal completion H⁰ algebra -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Every module is derived complete for the zero scalar. -/
lemma isModuleComplete_zero (M : ModuleCat.{u} R) : IsModuleComplete R 0 M :=
  isModuleComplete_of_pow_smul_zero R 0 M 1 (by intro x; simp)

/-- Forget the zero coordinate using the original two-coordinate algebra universal property. -/
def pairCompletionZeroToPrincipal (a : R) :
    letI := pairCompletionCommRing R a 0
    letI := pairCompletionAlgebra R a 0
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PairCompletionH0 R a 0 →ₐ[R] PrincipalCompletionH0 R a :=
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  pairCompletionLiftAlgHom R a 0 (PrincipalCompletionH0 R a)
    (principalCompletionH0_isModuleComplete R a) (isModuleComplete_zero R _)

/-- The inverse comparison is the original principal algebra universal extension. -/
def principalCompletionToPairZero (a : R) :
    letI := pairCompletionCommRing R a 0
    letI := pairCompletionAlgebra R a 0
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PrincipalCompletionH0 R a →ₐ[R] PairCompletionH0 R a 0 :=
  letI := pairCompletionCommRing R a 0
  letI := pairCompletionAlgebra R a 0
  principalCompletionLiftAlgHom R a (PairCompletionH0 R a 0)
    (pairCompletionH0_isModuleComplete_first R a 0)

/-- The two universal maps compose to the identity on the principal completion. -/
lemma pairCompletionZeroToPrincipal_comp (a : R) :
    letI := pairCompletionCommRing R a 0
    letI := pairCompletionAlgebra R a 0
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    (pairCompletionZeroToPrincipal R a).comp (principalCompletionToPairZero R a) =
      AlgHom.id R (PrincipalCompletionH0 R a) := by
  let := pairCompletionCommRing R a 0
  let := pairCompletionAlgebra R a 0
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact (principalCompletion_existsUnique_algHom R a (PrincipalCompletionH0 R a)
    (principalCompletionH0_isModuleComplete R a)).unique trivial trivial

/-- They also compose to the identity on the original two-coordinate completion. -/
lemma principalCompletionToPairZero_comp (a : R) :
    letI := pairCompletionCommRing R a 0
    letI := pairCompletionAlgebra R a 0
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    (principalCompletionToPairZero R a).comp (pairCompletionZeroToPrincipal R a) =
      AlgHom.id R (PairCompletionH0 R a 0) := by
  let := pairCompletionCommRing R a 0
  let := pairCompletionAlgebra R a 0
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact (pairCompletion_existsUnique_algHom R a 0 (PairCompletionH0 R a 0)
    (pairCompletionH0_isModuleComplete_first R a 0) (isModuleComplete_zero R _)).unique
    trivial trivial

/-- Adding a zero coordinate leaves the actual principal H⁰ algebra unchanged. -/
def pairCompletionZeroPrincipalAlgEquiv (a : R) :
    letI := pairCompletionCommRing R a 0
    letI := pairCompletionAlgebra R a 0
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PairCompletionH0 R a 0 ≃ₐ[R] PrincipalCompletionH0 R a := by
  letI := pairCompletionCommRing R a 0
  letI := pairCompletionAlgebra R a 0
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  exact
    { pairCompletionZeroToPrincipal R a with
      invFun := principalCompletionToPairZero R a
      left_inv := fun x ↦ congrArg (fun f ↦ f x) (principalCompletionToPairZero_comp R a)
      right_inv := fun x ↦ congrArg (fun f ↦ f x) (pairCompletionZeroToPrincipal_comp R a) }

/-- The algebra equivalence preserves the original coefficient ring unit. -/
lemma pairCompletionZeroPrincipalAlgEquiv_unit (a r : R) :
    letI := pairCompletionCommRing R a 0
    letI := pairCompletionAlgebra R a 0
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    pairCompletionZeroPrincipalAlgEquiv R a (pairCompletionUnitRingHom R a 0 r) =
      principalCompletionUnitRingHom R a r := by
  let := pairCompletionCommRing R a 0
  let := pairCompletionAlgebra R a 0
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact (pairCompletionZeroPrincipalAlgEquiv R a).commutes r

end SerrePositivity.DerivedCompletion
