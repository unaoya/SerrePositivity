module
public import SerrePositivity.HomologicalAlgebra.DerivedDiscretePointAction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReflection

/-! # Completion preserves multiplication by an original algebra point -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- A point-action map induces exactly multiplication in the actual H⁰ ring. -/
lemma derivedH0_pointAction
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    (x y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    letI := derivedH0CommRing A
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        (commMonPointAction A (boundedAboveUnitH0LinearEquiv A.X x)).hom y = x * y := by
  let := derivedH0CommRing A
  let := commMonUnitHomCommRing (DerivedCategory.Minus (ModuleCat R)) A
  apply (boundedAboveUnitH0LinearEquiv A.X).injective
  rw [boundedAboveUnitH0LinearEquiv_naturality]
  exact (commMonPointAction_sections A _ _).trans
    ((derivedH0UnitHomRingEquiv A).map_mul x y).symm

namespace DerivedCompletion
variable (R) (a : R)

/-- Completing the actual point-action map gives multiplication by its original unit-image. -/
lemma boundedAboveCompletion_pointAction
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    (p : 𝟙_ (DerivedCategory.Minus (ModuleCat R)) ⟶ A.X) :
    (boundedAboveDerivedCompletionFunctor R a).map (commMonPointAction A p) =
      commMonPointAction ((boundedAboveCompletionCommMonFunctor R a).obj A)
        (p ≫ (boundedAboveCompletionAlgebraUnit R a A).hom.hom) := by
  rw [boundedAboveCompletionAlgebraUnit_hom]
  apply InducedCategory.hom_ext
  apply derivedComplexCompletionHom_ext R a
    (derivedComplexCompletionFunctor_isComplete R a A.X.obj)
  have hn := (boundedAboveDerivedCompletionUnit R a).naturality (commMonPointAction A p)
  simp only [CategoryTheory.Functor.id_map] at hn
  have hm := commMonPointAction_naturality (boundedAboveCompletionAlgebraUnit R a A) p
  rw [boundedAboveCompletionAlgebraUnit_hom] at hm
  exact congrArg (fun f ↦ f.hom) (hn.symm.trans hm)

/-- The completed point-action acts on actual H⁰ by multiplication by the original H⁰ unit-image. -/
lemma boundedAboveCompletion_pointAction_homology
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj)
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj) :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (commMonPointAction A (boundedAboveUnitH0LinearEquiv A.X x))).hom y =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A) x * y := by
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  rw [boundedAboveCompletion_pointAction, derivedH0AlgMap_apply]
  have hx := boundedAboveUnitH0LinearEquiv_naturality
    (X := A.X) (Y := ((boundedAboveCompletionCommMonFunctor R a).obj A).X)
    (boundedAboveCompletionAlgebraUnit R a A).hom.hom x
  rw [← hx]
  exact derivedH0_pointAction _ _ _

/-- Ordinary coefficient multiplication completes to multiplication by its standard H⁰ image. -/
lemma boundedAboveCompletion_discrete_mul_homology
    (A : Type u) [CommRing A] [Algebra R A] (b : A)
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj
        (boundedAboveDerivedAlgebra (R := R) A)).X.obj) :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj
      (boundedAboveDerivedAlgebra (R := R) A))
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R b)))).hom y =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) A))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R A) b) * y := by
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj
    (boundedAboveDerivedAlgebra (R := R) A))
  have h := boundedAboveCompletion_pointAction_homology R a
    (boundedAboveDerivedAlgebra (R := R) A)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R A) b) y
  rw [boundedAboveDerivedAlgebra_pointAction_singleH0] at h
  exact h

/-- Over the coefficient ring itself, completed multiplication is its original scalar action. -/
lemma boundedAboveCompletion_coefficient_smul_homology (r : R)
    (y : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj
        (boundedAboveDerivedAlgebra (R := R) R)).X.obj) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
        ((boundedAboveDerivedCompletionFunctor R a).map
          (boundedAboveDerivedSingleFunctor.map (ModuleCat.ofHom (LinearMap.mulLeft R r)))).hom y =
      r • y := by
  let : CommRing ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) :=
    derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) R)
  let : Algebra R ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) :=
    derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) R)
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj
    (boundedAboveDerivedAlgebra (R := R) R))
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj
    (boundedAboveDerivedAlgebra (R := R) R))
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) R)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) R)
  have hr : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R R) r = algebraMap R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) r :=
    (derivedSingleH0AlgEquiv (R := R) R).symm.commutes r
  have h := boundedAboveCompletion_discrete_mul_homology R a R r y
  erw [hr, AlgHom.commutes] at h
  exact h.trans (Algebra.smul_def r y).symm

end DerivedCompletion
end SerrePositivity
