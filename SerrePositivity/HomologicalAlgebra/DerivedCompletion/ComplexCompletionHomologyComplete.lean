module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerHomologyComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ReflectionTransport

/-! # Actual homology modules of arbitrary derived complete objects are complete -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- Every homology module of a power-Koszul stage is complete, without bounds on its source. -/
lemma complexPowerKoszulStage_homology_isModuleComplete
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) (i : ℤ) :
    IsModuleComplete R a ((complexPowerKoszulStage R a K n).homology i) := by
  apply isModuleComplete_of_pow_smul_zero R a _ n
  have h := (scalarConeCoordinateNullHomotopy (a ^ n) K).homologyMap_eq i
  rw [smulId, homologyMap_smul, homologyMap_id, homologyMap_zero] at h
  intro x
  exact congrArg (fun f ↦ f.hom x) h

/-- All homology of the concrete completion is complete, retaining both Milnor contributions. -/
lemma complexCompletionFunctor_homology_isModuleComplete
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    IsModuleComplete R a (((complexCompletionFunctor R a).obj K).homology i) :=
  complexTowerHomology_isModuleComplete_of_stages R a
    (complexPowerKoszulStage R a K) (complexPowerKoszulTransition R a K) i
    (fun n ↦ complexPowerKoszulStage_homology_isModuleComplete R a K n (i - 1))
    (fun n ↦ complexPowerKoszulStage_homology_isModuleComplete R a K n i)

/-- The actual completion functor has complete actual homology modules in every degree. -/
lemma derivedComplexCompletionFunctor_homology_isModuleComplete
    (X : ConcreteDerivedCategory R) (i : ℤ) :
    IsModuleComplete R a ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedComplexCompletionFunctor R a).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : complexCompletionObject R a K ≅ (derivedComplexCompletionFunctor R a).obj X :=
    (derivedComplexCompletionComparison R a).symm.app K ≪≫
      (derivedComplexCompletionFunctor R a).mapIso (DerivedCategory.Q.objObjPreimageIso X)
  let h := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).symm.app
      ((complexCompletionFunctor R a).obj K) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e
  exact isModuleComplete_of_linearEquiv R a _ _ h.toLinearEquiv
    (complexCompletionFunctor_homology_isModuleComplete R a K i)

/-- Derived completeness implies module completeness of every actual homology module. -/
lemma isComplete_homology_isModuleComplete
    (X : ConcreteDerivedCategory R) (hX : IsComplete R a X) (i : ℤ) :
    IsModuleComplete R a ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
    (derivedComplexCompletionUnitIso R a X hX).symm
  exact isModuleComplete_of_linearEquiv R a _ _ e.toLinearEquiv
    (derivedComplexCompletionFunctor_homology_isModuleComplete R a X i)

end SerrePositivity.DerivedCompletion
