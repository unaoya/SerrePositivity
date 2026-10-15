module

public import SerrePositivity.HomologicalAlgebra.DerivedUnitHomology

/-! # Naturality of unit representability on actual cochain morphisms -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory HomologicalComplex CochainComplex.HomComplex
attribute [local instance] HasDerivedCategory.standard cochainTensorUnit_isKProjective
variable {R : Type u} [CommRing R]

/-- The induced cohomology-class map uses the canonical Hom-complex homology data. -/
def unitHomClassMapData
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) n).map
        (unitLinearHomMap f))
      (linearLeftHomologyData R (cochainTensorUnit (R := R)) K n)
      (linearLeftHomologyData R (cochainTensorUnit (R := R)) L n) := default

/-- On cycles the induced map is genuine cocycle postcomposition. -/
theorem unitHomClassMapData_cycles
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ)
    (x : Cocycle (cochainTensorUnit (R := R)) K n) :
    (unitHomClassMapData f n).φK x = x.postcomp f := by
  apply Subtype.ext
  exact congrArg (fun k ↦ k.hom x) (unitHomClassMapData f n).commi

/-- The actual induced homology map sends a cocycle class to its postcomposition class. -/
theorem unitHomClassMapData_class
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ)
    (x : Cocycle (cochainTensorUnit (R := R)) K n) :
    (unitHomClassMapData f n).φH (CohomologyClass.mk x) =
      CohomologyClass.mk (x.postcomp f) := by
  have h := congrArg (fun k ↦ k.hom x) (unitHomClassMapData f n).commπ
  change (unitHomClassMapData f n).φH (CohomologyClass.mk x) =
    CohomologyClass.mk ((unitHomClassMapData f n).φK x) at h
  rw [unitHomClassMapData_cycles] at h
  exact h

/-- The canonical linear Hom cohomology comparison is natural for actual Hom-complex maps. -/
theorem unitHomologyLinearEquiv_map
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ)
    (x : (CochainComplex.linearHomComplex R (cochainTensorUnit (R := R)) K).homology n) :
    homologyLinearEquiv R _ L n (homologyMap (unitLinearHomMap f) n x) =
      (unitHomClassMapData f n).φH (homologyLinearEquiv R _ K n x) := by
  have h := ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) n).map (unitLinearHomMap f))
    (linearLeftHomologyData R (cochainTensorUnit (R := R)) K n)
    (linearLeftHomologyData R (cochainTensorUnit (R := R)) L n)
  rw [(unitHomClassMapData f n).leftHomologyMap'_eq] at h
  exact (congrArg (fun k ↦ k.hom x) h).symm

/-- Unit representability commutes with actual cochain cohomology maps in every degree. -/
theorem unitCochainHomologyDerivedLinearEquiv_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℤ)
    (x : K.homology n) :
    unitCochainHomologyDerivedLinearEquiv L n (homologyMap f n x) =
      unitCochainHomologyDerivedLinearEquiv K n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  obtain ⟨v, rfl⟩ := (unitLinearHomHomologyIso K n).toLinearEquiv.surjective x
  have h := congrArg (fun k ↦ k.hom v) (unitLinearHomHomologyIso_naturality f n)
  change (unitLinearHomHomologyIso L n).hom (homologyMap (unitLinearHomMap f) n v) =
    homologyMap f n ((unitLinearHomHomologyIso K n).hom v) at h
  change unitCochainHomologyDerivedLinearEquiv L n
      (homologyMap f n ((unitLinearHomHomologyIso K n).hom v)) =
    unitCochainHomologyDerivedLinearEquiv K n ((unitLinearHomHomologyIso K n).hom v) ≫
      (DerivedCategory.Q.map f)⟦n⟧'
  rw [← h, unitCochainHomologyDerivedLinearEquiv_representative,
    unitCochainHomologyDerivedLinearEquiv_representative, unitHomologyLinearEquiv_map]
  obtain ⟨c, hc⟩ := (homologyLinearEquiv R (cochainTensorUnit (R := R)) K n v).mk_surjective
  rw [← hc, unitHomClassMapData_class]
  exact kProjectiveCohomologyDerivedLinearEquiv_postcomp _ f n c

end SerrePositivity
