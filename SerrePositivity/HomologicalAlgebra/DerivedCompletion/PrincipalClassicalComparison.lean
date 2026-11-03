module

public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Algebra
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
/-! # Regular principal completion H0 is the classical adic completion

The original actual H0 and its original unit are retained. Regularity supplies
classical completeness; the two algebra universal properties give inverse maps.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (ha : IsSMulRegular R a)

include ha in
/-- A regular scalar acts injectively on the original principal completion H0. -/
lemma principalCompletionH0_smul_injective_of_regular :
    Function.Injective (fun x : PrincipalCompletionH0 R a => a • x) := by
  let X0 := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)
  let X := (boundedAboveDerivedCompletionFunctor R a).obj X0
  have hc := derivedComplexCompletionFunctor_isComplete R a X0.obj
  have hpure : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj) := by
    intro i hi
    let ec : (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X ≅
        (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X0 := by
      have e := (boundedAboveDerivedCompletionQuotientIso R a ha 1 X0).symm
      rw [pow_one] at e
      exact e
    let e := ec ≪≫ derivedQuotientModuleIsoOfRegular a ha (ModuleCat.of R R) ha
    exact (derivedSingleHomology_isZero _ i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).mapIso
        (DerivedCategory.Minus.ι.mapIso e))
  have hreg := (derived_pure_of_complete_regular_quotient_pure a ha X hc hpure).2.2
  let e := (principalCompletedUnitH0Iso R a).toLinearEquiv
  intro x y hxy
  apply e.symm.injective
  apply hreg
  change a • e.symm x = a • e.symm y
  change a • x = a • y at hxy
  rw [← e.symm.map_smul, ← e.symm.map_smul, hxy]

include ha in
/-- The actual principal completion H0 is classically complete for a regular scalar. -/
lemma principalCompletionH0_isAdicComplete_of_regular :
    IsAdicComplete (Ideal.span {a}) (PrincipalCompletionH0 R a) :=
  (isModuleComplete_iff_isAdicComplete_of_regular R a _
    (principalCompletionH0_smul_injective_of_regular R a ha)).mp
      (principalCompletionH0_isModuleComplete R a)


/-- The original principal H0 universal map into the classical completion. -/
def principalCompletionToAdic :
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PrincipalCompletionH0 R a →ₐ[R] AdicCompletion (Ideal.span {a}) R := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  let : IsAdicComplete (Ideal.span {a}) (AdicCompletion (Ideal.span {a}) R) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (Set.toFinite _))
  exact principalCompletionLiftAlgHom R a (AdicCompletion (Ideal.span {a}) R)
    (isModuleComplete_of_isAdicComplete R a _)

/-- The classical completion extends the original map into principal H0. -/
def adicCompletionToPrincipal :
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    AdicCompletion (Ideal.span {a}) R →ₐ[R] PrincipalCompletionH0 R a := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  let : IsAdicComplete (Ideal.span {a}) (PrincipalCompletionH0 R a) :=
    principalCompletionH0_isAdicComplete_of_regular R a ha
  exact adicCompletionToCompleteAlgebra R (Ideal.span {a}) (Submodule.fg_span (Set.toFinite _)) _

/-- The two universal maps compose to the identity on the classical completion. -/
lemma principalCompletionToAdic_comp_adicCompletionToPrincipal :
    let := principalCompletionCommRing R a
    let := principalCompletionAlgebra R a
    (principalCompletionToAdic R a).comp (adicCompletionToPrincipal R a ha) =
      AlgHom.id R (AdicCompletion (Ideal.span {a}) R) := by
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  let : IsAdicComplete (Ideal.span {a}) (AdicCompletion (Ideal.span {a}) R) :=
    AdicCompletion.isAdicComplete (Submodule.fg_span (Set.toFinite _))
  exact adicCompletion_algHom_ext R (Ideal.span {a}) (Submodule.fg_span (Set.toFinite _)) _ _ _

/-- They also compose to the identity on the actual principal H0. -/
lemma adicCompletionToPrincipal_comp_principalCompletionToAdic :
    let := principalCompletionCommRing R a
    let := principalCompletionAlgebra R a
    (adicCompletionToPrincipal R a ha).comp (principalCompletionToAdic R a) =
      AlgHom.id R (PrincipalCompletionH0 R a) := by
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact (principalCompletion_existsUnique_algHom R a (PrincipalCompletionH0 R a)
    (principalCompletionH0_isModuleComplete R a)).unique trivial trivial

/-- The original principal H0 algebra is the classical completion algebra. -/
def principalCompletionAdicAlgEquiv :
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    PrincipalCompletionH0 R a ≃ₐ[R] AdicCompletion (Ideal.span {a}) R := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  refine AlgEquiv.ofAlgHom (principalCompletionToAdic R a) (adicCompletionToPrincipal R a ha) ?_ ?_
  · exact principalCompletionToAdic_comp_adicCompletionToPrincipal R a ha
  · exact adicCompletionToPrincipal_comp_principalCompletionToAdic R a ha

/-- The comparison preserves the original principal completion unit. -/
lemma principalCompletionAdicAlgEquiv_unit (r : R) :
    let := principalCompletionCommRing R a
    let := principalCompletionAlgebra R a
    principalCompletionAdicAlgEquiv R a ha (principalCompletionUnitRingHom R a r) =
      algebraMap R (AdicCompletion (Ideal.span {a}) R) r := by
  let := principalCompletionCommRing R a
  let := principalCompletionAlgebra R a
  exact (principalCompletionAdicAlgEquiv R a ha).commutes r
end SerrePositivity.DerivedCompletion
