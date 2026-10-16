module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraUnitNormalization

/-! # The actual completion H⁰ of any base algebra is its principal completion algebra -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (B : Type u) [CommRing B] [Algebra R B]

/-- Upgrade the original coefficient comparison using the principal module reflection. -/
def completedAlgebraPrincipalH0AlgEquiv :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    letI := principalCompletionCommRing B (algebraMap R B a)
    letI := principalCompletionAlgebra B (algebraMap R B a)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj ≃ₐ[B]
      PrincipalCompletionH0 B (algebraMap R B a) := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := completedAlgebraScalarAlgebra R a B
  letI := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
  letI := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
  letI := principalCompletionCommRing B (algebraMap R B a)
  letI := principalCompletionAlgebra B (algebraMap R B a)
  let E := (completedAlgebraRestrictionH0BLinearEquiv R a B).trans
    (principalCompletedUnitH0AlgEquiv B (algebraMap R B a)).toLinearEquiv
  let h := principalCompletionH0_isCompleteModuleReflection B (algebraMap R B a)
  have hT : ∀ _j : Fin 1, IsModuleComplete B (algebraMap R B a)
      (ModuleCat.of B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedAlgebra R a B).X.obj)) := fun _ ↦ completedAlgebraH0_isModuleComplete R a B
  have h1 : E.symm (koszulCompletionH0Unit B (fun _ : Fin 1 ↦ algebraMap R B a) 1) = 1 := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    change _ = (principalCompletedUnitH0AlgEquiv B (algebraMap R B a))
      ((completedAlgebraRestrictionH0Iso R a B).hom 1)
    rw [completedAlgebraRestrictionH0Iso_one]
    exact (principalCompletedUnitH0Iso_one B (algebraMap R B a)).symm
  exact (AlgEquiv.ofLinearEquiv E.symm h1
    (h.linearMap_map_mul _ hT E.symm.toLinearMap h1)).symm

/-- The algebra comparison has the original G8 and principal comparison as its function. -/
lemma completedAlgebraPrincipalH0AlgEquiv_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    letI := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
    letI := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
    letI := principalCompletionCommRing B (algebraMap R B a)
    letI := principalCompletionAlgebra B (algebraMap R B a)
    completedAlgebraPrincipalH0AlgEquiv R a B x =
      principalCompletedUnitH0AlgEquiv B (algebraMap R B a)
        ((completedAlgebraRestrictionH0Iso R a B).hom x) := rfl

/-- The ring comparison preserves the original completion map on every coefficient. -/
lemma completedAlgebraPrincipalH0AlgEquiv_unit (b : B) :
    let := derivedH0CommRing (completedAlgebra R a B)
    let := derivedH0Algebra (completedAlgebra R a B)
    let := completedAlgebraScalarAlgebra R a B
    let := principalCompletionCommRing B (algebraMap R B a)
    let := principalCompletionAlgebra B (algebraMap R B a)
    completedAlgebraPrincipalH0AlgEquiv R a B (completedAlgebraUnitAlgHom R a B b) =
      principalCompletionUnitRingHom B (algebraMap R B a) b := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := completedAlgebraScalarAlgebra R a B
  let := derivedH0CommRing (completedUnitAlgebra B (algebraMap R B a))
  let := derivedH0Algebra (completedUnitAlgebra B (algebraMap R B a))
  let := principalCompletionCommRing B (algebraMap R B a)
  let := principalCompletionAlgebra B (algebraMap R B a)
  rw [completedAlgebraPrincipalH0AlgEquiv_apply, completedAlgebraRestrictionH0Iso_unit,
    completedAlgebraUnitAlgHom_apply, principalCompletedUnitH0AlgEquiv_unit]

end SerrePositivity.DerivedCompletion
