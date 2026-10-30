module
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Scalar linearity of actual derived module homology -/
@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Actual derived module homology preserves the original ring's scalar action. -/
instance derivedModuleHomologyFunctor_linear (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).Linear R := by
  let : (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) n).Linear R :=
    ⟨fun _ _ ↦ homologyMap_smul _ _ _⟩
  let : Localization.Lifting
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
      (HomologicalComplex.homologyFunctor _ _ n)
      (DerivedCategory.homologyFunctor _ n) :=
    ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n⟩
  exact (Localization.functor_linear_iff
    (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) R
    (HomologicalComplex.homologyFunctor _ _ n)
    (DerivedCategory.homologyFunctor _ n)).mp inferInstance

end SerrePositivity
