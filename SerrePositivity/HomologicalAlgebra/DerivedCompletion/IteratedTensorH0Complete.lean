module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedAlgebraH0Comparison

/-! # Completeness of the original iterated completed tensor H⁰ for both coordinates -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (d : R)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "AP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "B" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AP).X.obj
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R d).obj AP).X.obj
/-- The original second completed H⁰ retains p-completeness as a ring. -/
lemma iteratedCompletedTensorH0_self_complete_p :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    IsModuleComplete C (p : C) (ModuleCat.of C C) := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := completionH0ScalarAlgebra R d AP
  let := completionH0ScalarTower R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  let P := PDCompletionH0 B p (algebraMap R B d)
  let e := iteratedCompletedTensorH0PDAlgEquiv R p d S T
  have hc : IsModuleComplete B (p : B) (ModuleCat.of B C) :=
    isModuleComplete_of_linearEquiv B (p : B) (ModuleCat.of B P) (ModuleCat.of B C)
      e.symm.toLinearEquiv (pairCompletionH0_isModuleComplete_first B (p : B) (algebraMap R B d))
  have ht := (isModuleComplete_algebraMap_iff B C (p : B) C).mpr hc
  simpa only [map_natCast] using ht

/-- The original image of d is a complete coordinate of the second actual H⁰ ring. -/
lemma iteratedCompletedTensorH0_self_complete_d :
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    IsModuleComplete C (algebraMap R C d) (ModuleCat.of C C) := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := completionH0ScalarAlgebra R d AP
  let := completionH0ScalarTower R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  let P := PDCompletionH0 B p (algebraMap R B d)
  let e := iteratedCompletedTensorH0PDAlgEquiv R p d S T
  have hc : IsModuleComplete B (algebraMap R B d) (ModuleCat.of B C) :=
    isModuleComplete_of_linearEquiv B (algebraMap R B d) (ModuleCat.of B P) (ModuleCat.of B C)
      e.symm.toLinearEquiv
      (pairCompletionH0_isModuleComplete_second B (p : B) (algebraMap R B d))
  have ht := (isModuleComplete_algebraMap_iff B C (algebraMap R B d) C).mpr hc
  simpa only [← IsScalarTower.algebraMap_apply R B C d] using ht

end SerrePositivity.DerivedCompletion
