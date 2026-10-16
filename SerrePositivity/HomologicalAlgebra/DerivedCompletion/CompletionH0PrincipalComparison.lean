module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0AlgebraUniversal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompleteFirstPairComparison
public import Mathlib.Algebra.Algebra.Tower

/-! # Actual completed derived-algebra H⁰ is principal completion of the original H⁰ -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
set_option quotPrecheck false in
local notation "B" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R a).obj A).X.obj
local notation "J" => derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a A)
/-- The coefficient H⁰(A) acts through the original H⁰ completion unit. -/
@[instance_reducible] def completionH0ScalarAlgebra :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    Algebra B C := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  exact (J).toRingHom.toAlgebra

/-- Its R-action is the original actual H⁰ action. -/
lemma completionH0ScalarTower :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    IsScalarTower R B C := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := completionH0ScalarAlgebra R a A
  exact IsScalarTower.of_algHom J

/-- Actual completed H⁰ is complete for the original coefficient image of a. -/
lemma completionH0_isModuleComplete_scalar :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    IsModuleComplete B (algebraMap R B a) (ModuleCat.of B C) := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := completionH0ScalarAlgebra R a A
  let := completionH0ScalarTower R a A
  exact (isModuleComplete_algebraMap_iff R B a C).mpr
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a A.X.obj 0)

variable [A.X.obj.IsLE 0]

/-- Compare actual completed H⁰ with principal completion of its original coefficient ring. -/
def completionH0PrincipalAlgEquiv :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    letI := principalCompletionCommRing B (algebraMap R B a)
    letI := principalCompletionAlgebra B (algebraMap R B a)
    C ≃ₐ[B] PrincipalCompletionH0 B (algebraMap R B a) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := completionH0ScalarAlgebra R a A
  letI := completionH0ScalarTower R a A
  let b := algebraMap R B a
  let P := PrincipalCompletionH0 B b
  letI := principalCompletionCommRing B b
  letI := principalCompletionAlgebra B b
  letI : Algebra R P := ((principalCompletionUnitRingHom B b).comp (algebraMap R B)).toAlgebra
  letI : IsScalarTower R B P := IsScalarTower.of_algebraMap_eq' rfl
  have hP : IsModuleComplete R a (ModuleCat.of R P) :=
    (isModuleComplete_algebraMap_iff R B a P).mp (principalCompletionH0_isModuleComplete B b)
  let f0 : B →ₐ[R] P := IsScalarTower.toAlgHom R B P
  let f := completionH0AlgebraLift R a A P hP f0
  have hf := completionH0AlgebraLift_unit R a A P hP f0
  let fB : C →ₐ[B] P :=
    { f.toRingHom with
      commutes' x := by
        change f (J x) = f0 x
        exact congrArg (fun h : B →ₐ[R] P => h x) hf }
  let g := (principalCompletion_existsUnique_algHom B b C
    (completionH0_isModuleComplete_scalar R a A)).choose
  have hfg : fB.comp g = AlgHom.id B P :=
    (principalCompletion_existsUnique_algHom B b P
      (principalCompletionH0_isModuleComplete B b)).unique trivial trivial
  have hc : IsModuleComplete R a (ModuleCat.of R C) :=
    derivedComplexCompletionFunctor_homology_isModuleComplete R a A.X.obj 0
  have hgf : g.comp fB = AlgHom.id B C := by
    apply AlgHom.restrictScalars_injective R
    apply AlgHom.toLinearMap_injective
    apply completionH0_linear_ext R a A C hc
    apply LinearMap.ext
    intro x
    change g (fB (J x)) = J x
    have hfBx := fB.commutes x
    change fB (J x) = algebraMap B P x at hfBx
    rw [hfBx]
    exact g.commutes x
  exact AlgEquiv.ofAlgHom fB g hfg hgf

/-- The comparison sends the original H⁰ unit to the original principal completion unit. -/
lemma completionH0PrincipalAlgEquiv_unit (x : B) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    letI := principalCompletionCommRing B (algebraMap R B a)
    letI := principalCompletionAlgebra B (algebraMap R B a)
    completionH0PrincipalAlgEquiv R a A (J x) =
      principalCompletionUnitRingHom B (algebraMap R B a) x := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := completionH0ScalarAlgebra R a A
  let := principalCompletionCommRing B (algebraMap R B a)
  let := principalCompletionAlgebra B (algebraMap R B a)
  exact (completionH0PrincipalAlgEquiv R a A).commutes x

/-- If the original H⁰ is already c-complete, actual a-completion is its pair completion. -/
def completionH0PairAlgEquivOfCompleteFirst (c : R)
    (hc : IsModuleComplete R c B) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    letI := pairCompletionCommRing B (algebraMap R B c) (algebraMap R B a)
    letI := pairCompletionAlgebra B (algebraMap R B c) (algebraMap R B a)
    C ≃ₐ[B] PairCompletionH0 B (algebraMap R B c) (algebraMap R B a) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  letI := completionH0ScalarAlgebra R a A
  letI := pairCompletionCommRing B (algebraMap R B c) (algebraMap R B a)
  letI := pairCompletionAlgebra B (algebraMap R B c) (algebraMap R B a)
  letI := principalCompletionCommRing B (algebraMap R B a)
  letI := principalCompletionAlgebra B (algebraMap R B a)
  have hb : IsModuleComplete B (algebraMap R B c) (ModuleCat.of B B) :=
    (isModuleComplete_algebraMap_iff R B c B).mpr hc
  exact (completionH0PrincipalAlgEquiv R a A).trans
    (pairCompletionPrincipalAlgEquivOfCompleteFirst B (algebraMap R B c)
      (algebraMap R B a) hb).symm

/-- The pair comparison retains the original completion unit on every H⁰ coefficient. -/
lemma completionH0PairAlgEquivOfCompleteFirst_unit (c : R)
    (hc : IsModuleComplete R c B) (x : B) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
    letI := completionH0ScalarAlgebra R a A
    letI := pairCompletionCommRing B (algebraMap R B c) (algebraMap R B a)
    letI := pairCompletionAlgebra B (algebraMap R B c) (algebraMap R B a)
    completionH0PairAlgEquivOfCompleteFirst R a A c hc (J x) =
      pairCompletionUnitRingHom B (algebraMap R B c) (algebraMap R B a) x := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R a).obj A)
  let := completionH0ScalarAlgebra R a A
  let := pairCompletionCommRing B (algebraMap R B c) (algebraMap R B a)
  let := pairCompletionAlgebra B (algebraMap R B c) (algebraMap R B a)
  exact (completionH0PairAlgEquivOfCompleteFirst R a A c hc).commutes x

end SerrePositivity.DerivedCompletion
