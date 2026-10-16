module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraRestriction
public import Mathlib.Algebra.Algebra.Tower

/-! # The coefficient algebra action on actual completion H⁰ -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (B : Type u) [CommRing B] [Algebra R B]

/-- The original standard completion unit is a map from B into actual completed H⁰. -/
def completedAlgebraUnitAlgHom :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    B →ₐ[R] (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R a B).X.obj := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := derivedH0Algebra (completedAlgebra R a B)
  letI : CommRing ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R B)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) B)
  letI : Algebra R ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R B)) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) B)
  letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) B)
  letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) B)
  exact (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
      (boundedAboveDerivedAlgebra (R := R) B))).comp
    (derivedSingleH0AlgEquiv (R := R) B).symm.toAlgHom

/-- Its function is the original actual completion map on the standard class of b. -/
lemma completedAlgebraUnitAlgHom_apply (b : B) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    completedAlgebraUnitAlgHom R a B b =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) B))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R B) b) := rfl

/-- Give actual completed H⁰ its coefficient B-algebra action via the original unit. -/
@[instance_reducible] def completedAlgebraScalarAlgebra :
    letI := derivedH0CommRing (completedAlgebra R a B)
    Algebra B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R a B).X.obj) := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := derivedH0Algebra (completedAlgebra R a B)
  exact (completedAlgebraUnitAlgHom R a B).toRingHom.toAlgebra

/-- The coefficient action forms the original R to B to completed H⁰ scalar tower. -/
lemma completedAlgebraScalarTower :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := derivedH0Algebra (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    IsScalarTower R B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R a B).X.obj) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := derivedH0Algebra (completedAlgebra R a B)
  let := completedAlgebraScalarAlgebra R a B
  exact IsScalarTower.of_algHom (completedAlgebraUnitAlgHom R a B)

/-- The original R-linear G8 H⁰ comparison is linear for the actual coefficient B action. -/
def completedAlgebraRestrictionH0BLinearEquiv :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj ≃ₗ[B]
      (DerivedCategory.homologyFunctor (ModuleCat B) 0).obj
        (completedUnitAlgebra B (algebraMap R B a)).X.obj := by
  letI := derivedH0CommRing (completedAlgebra R a B)
  letI := derivedH0Algebra (completedAlgebra R a B)
  letI := completedAlgebraScalarAlgebra R a B
  refine
    { (completedAlgebraRestrictionH0Iso R a B).toLinearEquiv.toEquiv with
      map_add' := (completedAlgebraRestrictionH0Iso R a B).toLinearEquiv.map_add
      map_smul' := ?_ }
  intro b y
  change (completedAlgebraRestrictionH0Iso R a B).hom
    (completedAlgebraUnitAlgHom R a B b * y) = _
  rw [completedAlgebraUnitAlgHom_apply]
  exact completedAlgebraRestrictionH0Iso_coefficient R a B b y

/-- This B-linear equivalence has exactly the same original G8 comparison function. -/
lemma completedAlgebraRestrictionH0BLinearEquiv_apply
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedAlgebra R a B).X.obj) :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    completedAlgebraRestrictionH0BLinearEquiv R a B y =
      (completedAlgebraRestrictionH0Iso R a B).hom y := rfl

/-- Actual H⁰ is complete over the coefficient algebra with its original unit action. -/
lemma completedAlgebraH0_isModuleComplete :
    letI := derivedH0CommRing (completedAlgebra R a B)
    letI := completedAlgebraScalarAlgebra R a B
    IsModuleComplete B (algebraMap R B a)
      (ModuleCat.of B ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedAlgebra R a B).X.obj)) := by
  let := derivedH0CommRing (completedAlgebra R a B)
  let := completedAlgebraScalarAlgebra R a B
  exact isModuleComplete_of_linearEquiv B (algebraMap R B a) _ _
    (completedAlgebraRestrictionH0BLinearEquiv R a B).symm
    (derivedComplexCompletionFunctor_homology_isModuleComplete B (algebraMap R B a)
      ((DerivedCategory.singleFunctor (ModuleCat B) 0).obj (ModuleCat.of B B)) 0)

end SerrePositivity.DerivedCompletion
