module

public import SerrePositivity.HomologicalAlgebra.UnitLinearHomComplex
public import SerrePositivity.HomologicalAlgebra.KProjectiveCohomologyLinear
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Actual derived cohomology represented by the unit object -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CochainComplex.HomComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- The actual tensor unit complex is K-projective. -/
theorem cochainTensorUnit_isKProjective : (cochainTensorUnit (R := R)).IsKProjective := by
  have : ∀ i, Projective ((cochainTensorUnit (R := R)).X i) := fun _ ↦ inferInstance
  exact CochainComplex.isKProjective_of_projective _ 0

attribute [local instance] cochainTensorUnit_isKProjective

/-- Every cohomology module is represented linearly by shifted maps from the actual unit. -/
def unitCochainHomologyDerivedLinearEquiv
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    K.homology n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj (cochainTensorUnit (R := R)))
        (DerivedCategory.Q.obj K) n := by
  exact (unitLinearHomHomologyIso K n).symm.toLinearEquiv ≪≫ₗ
    (CochainComplex.HomComplex.homologyLinearEquiv R _ K n) ≪≫ₗ
    kProjectiveCohomologyDerivedLinearEquiv _ K n

/-- The comparison computes exactly the localized cocycle representative. -/
theorem unitCochainHomologyDerivedLinearEquiv_representative
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : (CochainComplex.linearHomComplex R (cochainTensorUnit (R := R)) K).homology n) :
    unitCochainHomologyDerivedLinearEquiv K n ((unitLinearHomHomologyIso K n).hom x) =
      kProjectiveCohomologyDerivedEquiv _ K n
        (CochainComplex.HomComplex.homologyLinearEquiv R _ K n x) := by
  change (kProjectiveCohomologyDerivedEquiv _ K n)
    (CochainComplex.HomComplex.homologyLinearEquiv R _ K n
      ((unitLinearHomHomologyIso K n).inv ((unitLinearHomHomologyIso K n).hom x))) = _
  simp

/-- All actual derived cohomology modules admit the same linear representability comparison.
Naturality and its standard H⁰ evaluation normalization are verified separately. -/
def derivedUnitHomologyLinearEquiv
    (X : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) n).obj X ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj (cochainTensorUnit (R := R))) X n := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  let h : (DerivedCategory.homologyFunctor (ModuleCat R) n).obj X ≅ K.homology n :=
    ((DerivedCategory.homologyFunctor (ModuleCat R) n).mapIso e).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app K
  exact h.toLinearEquiv ≪≫ₗ unitCochainHomologyDerivedLinearEquiv K n ≪≫ₗ
    Linear.homCongr R (Iso.refl _) ((shiftFunctor _ n).mapIso e)

/-- In degree zero this yields ordinary actual derived Hom via the canonical zero-shift iso. -/
def derivedUnitH0HomLinearEquiv (X : DerivedCategory (ModuleCat.{u} R)) :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X ≃ₗ[R]
      (DerivedCategory.Q.obj (cochainTensorUnit (R := R)) ⟶ X) :=
  derivedUnitHomologyLinearEquiv X 0 ≪≫ₗ
    Linear.homCongr R (Iso.refl _) ((shiftFunctorZero _ ℤ).app X)

end SerrePositivity
