module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedAlgebraPrincipalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairZeroCompletion

/-! # The original F3 completion of any R-algebra compared as an R-algebra -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The original F3 algebra of B, regarded over its original base R. -/
@[instance_reducible] def pdCompletionBaseAlgebra (p : ℕ) (d : B) :
    letI := pdCompletionCommRing B p d
    Algebra R (PDCompletionH0 B p d) := by
  letI := pdCompletionCommRing B p d
  exact ((pdCompletionUnit B p d).comp (algebraMap R B)).toAlgebra

/-- This coefficient restriction has the original R to B to F3 scalar tower. -/
lemma pdCompletionBaseScalarTower (p : ℕ) (d : B) :
    letI := pdCompletionCommRing B p d
    letI := pdCompletionAlgebra B p d
    letI := pdCompletionBaseAlgebra R B p d
    IsScalarTower R B (PDCompletionH0 B p d) := by
  let := pdCompletionCommRing B p d
  let := pdCompletionAlgebra B p d
  let := pdCompletionBaseAlgebra R B p d
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Completing B over R gives the original F3 (p,0) algebra, with its B-algebra structure. -/
def completedAlgebraH0PDBAlgEquiv (p : ℕ) :
    letI := derivedH0CommRing (completedAlgebra R (p : R) B)
    letI := completedAlgebraScalarAlgebra R (p : R) B
    letI := pdCompletionCommRing B p 0
    letI := pdCompletionAlgebra B p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R (p : R) B).X.obj ≃ₐ[B] PDCompletionH0 B p 0 := by
  letI := derivedH0CommRing (completedAlgebra R (p : R) B)
  letI := completedAlgebraScalarAlgebra R (p : R) B
  letI := pdCompletionCommRing B p 0
  letI := pdCompletionAlgebra B p 0
  letI := principalCompletionCommRing B (p : B)
  letI := principalCompletionAlgebra B (p : B)
  have aux (c : B) (hc : algebraMap R B (p : R) = c) :
      letI := principalCompletionCommRing B c
      letI := principalCompletionAlgebra B c
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedAlgebra R (p : R) B).X.obj ≃ₐ[B] PrincipalCompletionH0 B c := by
    subst c
    exact completedAlgebraPrincipalH0AlgEquiv R (p : R) B
  let e := aux (p : B) (map_natCast (algebraMap R B) p)
  exact e.trans (pairCompletionZeroPrincipalAlgEquiv B (p : B)).symm

/-- The comparison is an R-algebra equivalence for the original actual H⁰ algebra structure. -/
def completedAlgebraH0PDAlgEquiv (p : ℕ) :
    letI := derivedH0CommRing (completedAlgebra R (p : R) B)
    letI := derivedH0Algebra (completedAlgebra R (p : R) B)
    letI := pdCompletionCommRing B p 0
    letI := pdCompletionBaseAlgebra R B p 0
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (completedAlgebra R (p : R) B).X.obj ≃ₐ[R] PDCompletionH0 B p 0 := by
  letI := derivedH0CommRing (completedAlgebra R (p : R) B)
  letI := derivedH0Algebra (completedAlgebra R (p : R) B)
  letI := completedAlgebraScalarAlgebra R (p : R) B
  letI := completedAlgebraScalarTower R (p : R) B
  letI := pdCompletionCommRing B p 0
  letI := pdCompletionAlgebra B p 0
  letI := pdCompletionBaseAlgebra R B p 0
  letI := pdCompletionBaseScalarTower R B p 0
  exact (completedAlgebraH0PDBAlgEquiv R B p).restrictScalars R

/-- Every coefficient keeps its original image in the F3 comparison. -/
lemma completedAlgebraH0PDAlgEquiv_unit (p : ℕ) (b : B) :
    letI := derivedH0CommRing (completedAlgebra R (p : R) B)
    letI := derivedH0Algebra (completedAlgebra R (p : R) B)
    letI := pdCompletionCommRing B p 0
    letI := pdCompletionBaseAlgebra R B p 0
    completedAlgebraH0PDAlgEquiv R B p (completedAlgebraUnitAlgHom R (p : R) B b) =
      pdCompletionUnit B p 0 b := by
  let := derivedH0CommRing (completedAlgebra R (p : R) B)
  let := derivedH0Algebra (completedAlgebra R (p : R) B)
  let := completedAlgebraScalarAlgebra R (p : R) B
  let := pdCompletionCommRing B p 0
  let := pdCompletionAlgebra B p 0
  let := pdCompletionBaseAlgebra R B p 0
  exact (completedAlgebraH0PDBAlgEquiv R B p).commutes b

end SerrePositivity.DerivedCompletion
