import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0AlgebraUniversal
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.algHomOfDenseLinearExtension
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0_linear_ext
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0AlgebraLift
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0AlgebraLift_unit
assert_no_sorry SerrePositivity.DerivedCompletion.completionH0_existsUnique_algHom

#print axioms SerrePositivity.DerivedCompletion.algHomOfDenseLinearExtension
#print axioms SerrePositivity.DerivedCompletion.completionH0_linear_ext
#print axioms SerrePositivity.DerivedCompletion.completionH0AlgebraLift
#print axioms SerrePositivity.DerivedCompletion.completionH0AlgebraLift_unit
#print axioms SerrePositivity.DerivedCompletion.completionH0_existsUnique_algHom

noncomputable section
universe u
open CategoryTheory SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a d : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))) [A.X.obj.IsLE 0]
    (T : Type u) [CommRing T] [Algebra R T]
    (hT : IsModuleComplete R d (ModuleCat.of R T))

-- The actual next d-completion of the original a-completed algebra is covered.
example :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj A))
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj
      ((boundedAboveCompletionCommMonFunctor R a).obj A))
    ∀ f : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj →ₐ[R] T,
      ∃! g : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          ((boundedAboveCompletionCommMonFunctor R d).obj
            ((boundedAboveCompletionCommMonFunctor R a).obj A)).X.obj →ₐ[R] T,
        g.comp (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R d
          ((boundedAboveCompletionCommMonFunctor R a).obj A))) = f := by
  let hle : ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj.IsLE 0 :=
    boundedAboveDerivedCompletionFunctor_isLE R a A.X 0 inferInstance
  exact completionH0_existsUnique_algHom R d
    ((boundedAboveCompletionCommMonFunctor R a).obj A) T hT

-- No regularity is imposed on the completion coordinate, including zero.
example (h0 : IsModuleComplete R 0 (ModuleCat.of R T)) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R 0).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R 0).obj A)
    ∀ f : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj →ₐ[R] T,
      ∃! g : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          ((boundedAboveCompletionCommMonFunctor R 0).obj A).X.obj →ₐ[R] T,
        g.comp (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R 0 A)) = f :=
  completionH0_existsUnique_algHom R 0 A T h0
