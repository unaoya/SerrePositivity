module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-! # Linear cohomology-class representatives of actual derived morphisms -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Localization
open CochainComplex.HomComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

local instance smallLocalizedShiftedHom (P K : CochainComplex (ModuleCat.{u} R) ℤ) :
    HasSmallLocalizedShiftedHom.{u + 1}
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)) ℤ P K := fun m n ↦
  hasSmallLocalizedHom_of_isLocalization
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
    (DerivedCategory.Q (C := ModuleCat R)) (X := P⟦m⟧) (Y := K⟦n⟧)

/-- K-projective cohomology classes represent all actual derived morphisms of the given degree. -/
def kProjectiveCohomologyDerivedEquiv
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] (n : ℤ) :
    CohomologyClass P K n ≃ ShiftedHom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K) n :=
  (CohomologyClass.equivOfIsKProjective.{u + 1}).trans
    (SmallShiftedHom.equiv _ DerivedCategory.Q)

/-- A cocycle represents its actual localized shifted chain map. -/
theorem kProjectiveCohomologyDerivedEquiv_mk
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] (n : ℤ)
    (x : Cocycle P K n) :
    kProjectiveCohomologyDerivedEquiv P K n (.mk x) =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q :=
  CohomologyClass.equiv_toSmallShiftedHom_mk x

/-- This comparison respects the existing R-module structures on cohomology and derived Hom. -/
def kProjectiveCohomologyDerivedLinearEquiv
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] (n : ℤ) :
    CohomologyClass P K n ≃ₗ[R]
      ShiftedHom (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K) n where
  toEquiv := kProjectiveCohomologyDerivedEquiv P K n
  map_add' x y := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← CohomologyClass.mk_add]
    simp only [Equiv.toFun_as_coe, kProjectiveCohomologyDerivedEquiv_mk, map_add, ShiftedHom.map,
      Functor.map_add, CategoryTheory.Preadditive.add_comp]
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    rw [← CohomologyClass.mk_smul]
    simp [kProjectiveCohomologyDerivedEquiv_mk, ShiftedHom.map]

/-- The linear comparison has the same cocycle normalization as the original equivalence. -/
theorem kProjectiveCohomologyDerivedLinearEquiv_mk
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] (n : ℤ)
    (x : Cocycle P K n) :
    kProjectiveCohomologyDerivedLinearEquiv P K n (.mk x) =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q :=
  kProjectiveCohomologyDerivedEquiv_mk P K n x

/-- Genuine cocycle postcomposition becomes composition with the shifted actual derived map. -/
theorem kProjectiveCohomologyDerivedLinearEquiv_postcomp
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ)
    (x : Cocycle P K n) :
    kProjectiveCohomologyDerivedLinearEquiv P L n (.mk (x.postcomp f)) =
      kProjectiveCohomologyDerivedLinearEquiv P K n (.mk x) ≫
        (DerivedCategory.Q.map f)⟦n⟧' := by
  rw [kProjectiveCohomologyDerivedLinearEquiv_mk,
    kProjectiveCohomologyDerivedLinearEquiv_mk, Cocycle.equivHomShift_symm_postcomp]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]

end SerrePositivity
