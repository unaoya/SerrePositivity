import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteScalarConePurity
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.DerivedCompletion.isZero_of_complete_of_smul_surjective
assert_no_sorry SerrePositivity.DerivedCompletion.cochain_homology_smul_surjective_of_scalarCone_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.cochain_homology_smul_injective_of_scalarCone_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.derived_homology_smul_surjective_of_scalarCone_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.derived_homology_smul_injective_of_scalarCone_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.derived_homology_isZero_of_complete_of_scalarCone_isZero
assert_no_sorry SerrePositivity.DerivedCompletion.derived_pure_of_complete_scalarCone_pure
assert_no_sorry SerrePositivity.DerivedCompletion.derived_pure_of_complete_regular_quotient_pure

#print axioms SerrePositivity.DerivedCompletion.isZero_of_complete_of_smul_surjective
#print axioms SerrePositivity.DerivedCompletion.cochain_homology_smul_surjective_of_scalarCone_isZero
#print axioms SerrePositivity.DerivedCompletion.cochain_homology_smul_injective_of_scalarCone_isZero
#print axioms SerrePositivity.DerivedCompletion.derived_homology_smul_surjective_of_scalarCone_isZero
#print axioms SerrePositivity.DerivedCompletion.derived_homology_smul_injective_of_scalarCone_isZero
#print axioms SerrePositivity.DerivedCompletion.derived_homology_isZero_of_complete_of_scalarCone_isZero
#print axioms SerrePositivity.DerivedCompletion.derived_pure_of_complete_scalarCone_pure
#print axioms SerrePositivity.DerivedCompletion.derived_pure_of_complete_regular_quotient_pure

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SerrePositivity SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

-- X is an arbitrary actual derived object: neither bound nor ring regularity is assumed.
example (X : ConcreteDerivedCategory R) (hc : IsComplete R a X)
    (h : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    X.IsGE 0 ∧ X.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X => a • x) :=
  derived_pure_of_complete_scalarCone_pure a X hc h

-- The ordinary quotient version explicitly retains ring regularity.
example (ha : IsSMulRegular R a) (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hc : IsComplete R a X.obj)
    (h : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj)) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧ Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => a • x) :=
  derived_pure_of_complete_regular_quotient_pure a ha X hc h

-- No adic separation or bounded torsion is required on the module.
example (M : ModuleCat.{u} R) (hc : IsModuleComplete R a M)
    (hs : Function.Surjective (fun x : M => a • x)) : IsZero M :=
  isZero_of_complete_of_smul_surjective a M hc hs
