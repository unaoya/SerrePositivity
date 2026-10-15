module

public import SerrePositivity.HomologicalAlgebra.DerivedH0Algebra
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Normalization of the unit cohomology comparison on discrete objects -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory HomologicalComplex CochainComplex.HomComplex
attribute [local instance] HasDerivedCategory.standard cochainTensorUnit_isKProjective
variable {R : Type u} [CommRing R]

/-- A degree-zero cocycle represents the usual map followed by the canonical zero shift. -/
theorem equivHomShift_ofHom_zero
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom f) =
      f ≫ (shiftFunctorZero (CochainComplex (ModuleCat R) ℤ) ℤ).inv.app L := by
  apply (Cocycle.equivHomShift (K := K) (L := L) (n := 0)).injective
  apply Subtype.ext
  apply Cochain.ext
  intro i j hij
  obtain rfl : j = i := by omega
  simp [Cocycle.equivHomShift_apply, Cochain.rightUnshift_v,
    CochainComplex.shiftFunctorZero_inv_app_f]

/-- After removing the zero shift, a localized ordinary cocycle is its original derived map. -/
theorem kProjectiveCohomologyDerivedZero_ofHom
    {P K : CochainComplex (ModuleCat.{u} R) ℤ} [P.IsKProjective] (f : P ⟶ K) :
    kProjectiveCohomologyDerivedLinearEquiv P K 0 (.mk (Cocycle.ofHom f)) ≫
        (shiftFunctorZero (DerivedCategory (ModuleCat R)) ℤ).hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map f := by
  rw [kProjectiveCohomologyDerivedLinearEquiv_mk, equivHomShift_ofHom_zero]
  change (ShiftedHom.mk₀ 0 rfl f).map DerivedCategory.Q ≫
    (shiftFunctorZero (DerivedCategory (ModuleCat R)) ℤ).hom.app (DerivedCategory.Q.obj K) = _
  rw [ShiftedHom.map_mk₀]
  simp [ShiftedHom.mk₀, shiftFunctorZero']

/-- Hom-complex cycle classes evaluate to their coefficient in the standard single H⁰ iso. -/
theorem unitSingleHomology_cycle_normalization (M : ModuleCat.{u} R) :
    let K := (CochainComplex.singleFunctor (ModuleCat R) 0).obj M
    let h := linearLeftHomologyData R (cochainTensorUnit (R := R)) K 0
    h.π ≫ h.homologyIso.inv ≫ homologyMap (unitLinearHomComplexIso K).hom 0 ≫
        (singleObjHomologySelfIso (.up ℤ) 0 M).hom =
      h.i ≫ (unitLinearHomComplexIso K).hom.f 0 ≫ (singleObjXSelf (.up ℤ) 0 M).hom := by
  dsimp only
  rw [ShortComplex.LeftHomologyData.π_comp_homologyIso_inv_assoc]
  change _ ≫ (CochainComplex.linearHomComplex R cochainTensorUnit
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)).homologyπ 0 ≫ _ = _
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom]
  rw [← Category.assoc (cyclesMap _ _), cyclesMap_i]
  simp only [← Category.assoc]
  erw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles]

/-- A cocycle class maps to its evaluated coefficient under the canonical single H⁰ comparison. -/
theorem unitSingleHomology_class_normalization (M : ModuleCat.{u} R)
    (x : Cocycle (cochainTensorUnit (R := R))
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) 0) :
    (singleObjHomologySelfIso (.up ℤ) 0 M).hom
        ((unitLinearHomHomologyIso ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) 0).hom
          ((homologyLinearEquiv R (cochainTensorUnit (R := R))
            ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) 0).symm (.mk x))) =
      (singleObjXSelf (.up ℤ) 0 M).hom
        (unitHomCochainEquiv ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) 0 x.1) := by
  exact congrArg (fun k ↦ k.hom x) (unitSingleHomology_cycle_normalization M)

/-- An ordinary map from R evaluates to its value on one, with the standard single coefficients. -/
theorem unitHomCochainEquiv_ofHom_single (M : ModuleCat.{u} R)
    (g : ModuleCat.of R R ⟶ M) :
    (singleObjXSelf (.up ℤ) 0 M).hom
      (unitHomCochainEquiv ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) 0
        (Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat R) 0).map g))) = g.hom 1 := by
  change (((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv ≫
    ((CochainComplex.singleFunctor (ModuleCat R) 0).map g).f 0) ≫
      (singleObjXSelf (.up ℤ) 0 M).hom).hom 1 = g.hom 1
  erw [HomologicalComplex.single_map_f_self]
  simp

/-- The ordinary value on one and the localized single map have exactly the same H⁰ class. -/
theorem unitCochainHomologyDerivedLinearEquiv_single (M : ModuleCat.{u} R)
    (g : ModuleCat.of R R ⟶ M) :
    unitCochainHomologyDerivedLinearEquiv
        ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) 0
        ((singleObjHomologySelfIso (.up ℤ) 0 M).inv (g.hom 1)) ≫
      (shiftFunctorZero (DerivedCategory (ModuleCat R)) ℤ).hom.app
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat R) 0).map g) := by
  let K := (CochainComplex.singleFunctor (ModuleCat R) 0).obj M
  let x := Cocycle.ofHom ((CochainComplex.singleFunctor (ModuleCat R) 0).map g)
  let v := (homologyLinearEquiv R (cochainTensorUnit (R := R)) K 0).symm (.mk x)
  have hv : (singleObjHomologySelfIso (.up ℤ) 0 M).inv (g.hom 1) =
      (unitLinearHomHomologyIso K 0).hom v := by
    apply (singleObjHomologySelfIso (.up ℤ) 0 M).toLinearEquiv.injective
    change (singleObjHomologySelfIso (.up ℤ) 0 M).toLinearEquiv
        ((singleObjHomologySelfIso (.up ℤ) 0 M).toLinearEquiv.symm (g.hom 1)) =
      (singleObjHomologySelfIso (.up ℤ) 0 M).hom
        ((unitLinearHomHomologyIso K 0).hom v)
    rw [LinearEquiv.apply_symm_apply]
    exact ((unitSingleHomology_class_normalization M x).trans
      (unitHomCochainEquiv_ofHom_single M g)).symm
  rw [hv, unitCochainHomologyDerivedLinearEquiv_representative]
  change kProjectiveCohomologyDerivedLinearEquiv _ K 0
    (homologyLinearEquiv R (cochainTensorUnit (R := R)) K 0 v) ≫ _ = _
  dsimp only [v]
  rw [LinearEquiv.apply_symm_apply]
  exact kProjectiveCohomologyDerivedZero_ofHom _

/-- The standard derived single H⁰ comparison is the standard cochain comparison after Q. -/
theorem derivedSingleH0Iso_formula (M : ModuleCat.{u} R) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).hom.app M =
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).hom.app
        ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) ≫
        (singleObjHomologySelfIso (.up ℤ) 0 M).hom := by
  simp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.singleFunctorsPostcompQIso, HomologicalComplex.homologyFunctorSingleIso]

/-- Its inverse agrees with the cochain inverse through the standard factorization. -/
theorem derivedSingleH0Iso_inv_factors (M : ModuleCat.{u} R) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app M ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).hom.app
          ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M) =
      (singleObjHomologySelfIso (.up ℤ) 0 M).inv := by
  apply (cancel_mono (singleObjHomologySelfIso (.up ℤ) 0 M).hom).mp
  rw [Category.assoc, ← derivedSingleH0Iso_formula]
  simp

/-- The natural actual H⁰ comparison is normalized by the canonical single-object H⁰ iso. -/
theorem derivedUnitH0NaturalLinearEquiv_single (M : ModuleCat.{u} R)
    (g : ModuleCat.of R R ⟶ M) :
    derivedUnitH0NaturalLinearEquiv R ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app M
          (g.hom 1)) =
      (DerivedCategory.singleFunctor (ModuleCat R) 0).map g := by
  simp only [derivedUnitH0NaturalLinearEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  change derivedUnitHomologyNaturalLinearEquiv R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)) 0
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app M
        (g.hom 1)) ≫
    (shiftFunctorZero (DerivedCategory (ModuleCat R)) ℤ).hom.app
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)) =
    DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat R) 0).map g)
  rw [derivedUnitHomologyNaturalLinearEquiv_Q]
  have h := congrArg (fun k ↦ k.hom (g.hom 1)) (derivedSingleH0Iso_inv_factors M)
  change (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).hom.app
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj M)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app M (g.hom 1)) =
    (singleObjHomologySelfIso (.up ℤ) 0 M).inv (g.hom 1) at h
  rw [h]
  exact unitCochainHomologyDerivedLinearEquiv_single M g

/-- The identity class of the actual unit is exactly the standard single H⁰ class of one. -/
theorem derivedUnitH0IdentityClass_normalization :
    derivedUnitH0IdentityClass R =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R R) (1 : R) := by
  apply (derivedUnitH0NaturalLinearEquiv R
    (DerivedCategory.Q.obj (cochainTensorUnit (R := R)))).injective
  rw [derivedUnitH0IdentityClass, LinearEquiv.apply_symm_apply]
  change 𝟙 ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) =
    derivedUnitH0NaturalLinearEquiv R
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
        (ModuleCat.of R R) (1 : R))
  have h := derivedUnitH0NaturalLinearEquiv_single (ModuleCat.of R R) (𝟙 (ModuleCat.of R R))
  simpa only [ModuleCat.hom_id, LinearMap.id_apply, CategoryTheory.Functor.map_id] using h.symm

/-- The inverse comparison is evaluation of the actual H⁰ map on the standard class of one. -/
theorem derivedUnitH0NaturalLinearEquiv_symm_standardOne
    (X : DerivedCategory (ModuleCat.{u} R))
    (f : DerivedCategory.Q.obj (cochainTensorUnit (R := R)) ⟶ X) :
    (derivedUnitH0NaturalLinearEquiv R X).symm f =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R R) (1 : R)) := by
  rw [derivedUnitH0NaturalLinearEquiv_symm_apply, derivedUnitH0IdentityClass_normalization]

/-- The actual H⁰ ring unit is the original algebra unit applied to the standard H⁰ class of one. -/
theorem derivedH0_one_standard
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))) :
    letI := derivedH0CommRing A
    (1 : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) =
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map A.mon.one.hom
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R R) (1 : R)) := by
  let := derivedH0CommRing A
  have h : (derivedUnitH0NaturalLinearEquiv R A.X.obj).symm A.mon.one.hom =
      (1 : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) := by
    apply (derivedUnitH0NaturalLinearEquiv R A.X.obj).injective
    rw [LinearEquiv.apply_symm_apply]
    change A.mon.one.hom = (boundedAboveUnitH0LinearEquiv A.X 1).hom
    rw [derivedH0_one_normalization]
  exact h.symm.trans (derivedUnitH0NaturalLinearEquiv_symm_standardOne A.X.obj A.mon.one.hom)

end SerrePositivity
