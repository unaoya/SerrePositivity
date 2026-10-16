module
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat
public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeComparison
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor

/-! # Complete flatness from an acyclic flat residue module -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Give the ordinary quotient-tensor comparison its original quotient-ring linearity. -/
def quotientTensorReductionEquiv (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R ⧸ I] AdicReduction I M := by
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro r x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  change e ((algebraMap R (R ⧸ I) r) • x) = (algebraMap R (R ⧸ I) r) • e x
  rw [algebraMap_smul (R ⧸ I), algebraMap_smul (R ⧸ I)]
  exact e.map_smul r x

/-- No regularity is needed once the actual residue extension is acyclic and flat. -/
theorem isCompletelyFlat_of_acyclic_flat_reduction (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M]
    (hTor : scalarExtensionTorVanishing (Ideal.Quotient.mk I) (ModuleCat.of R M))
    (hFlat : Module.Flat (R ⧸ I)
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of R M))) :
    IsCompletelyFlat I M := by
  intro N _ _ hN
  have hNt : Module.IsTorsionBySet R N (I : Set R) := fun {x} {r} ↦ hN r r.property x
  let := hNt.module
  let NQ := ModuleCat.of (R ⧸ I) N
  let E : (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj NQ ≃ₗ[R] N :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  apply (isConcentratedInDegreeZero_derivedTensor_iff M N).mpr
  intro i hi
  have hz := tor_isZero_of_acyclicBaseChange_flat (Ideal.Quotient.mk I)
    (ModuleCat.of R M) hTor hFlat NQ i hi
  have hz' : IsZero (((Tor (ModuleCat R) i).obj (ModuleCat.of R N)).obj (ModuleCat.of R M)) :=
    hz.of_iso (((Tor (ModuleCat R) i).mapIso E.toModuleIso).app (ModuleCat.of R M)).symm
  have := ModuleCat.subsingleton_of_isZero hz'
  exact (torModuleComm (R := R) i M N).injective.subsingleton

/-- G3: regularity on R and M and flatness of M/aM imply the original complete flatness. -/
theorem isCompletelyFlat_principal_of_regular (a : R) (ha : IsSMulRegular R a)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsSMulRegular M a)
    (hFlat : Module.Flat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M)) :
    IsCompletelyFlat (Ideal.span {a}) M := by
  have := hFlat
  let e := (quotientScalarExtensionEquiv (Ideal.span {a}) (ModuleCat.of R M)).trans
    (quotientTensorReductionEquiv (Ideal.span {a}) M).symm
  exact isCompletelyFlat_of_acyclic_flat_reduction (Ideal.span {a}) M
    (scalarExtensionTorVanishing_principal_of_regular a ha (ModuleCat.of R M) hM)
    (Module.Flat.of_linearEquiv e)

/-- The same criterion with a faithfully flat residue gives complete faithful flatness. -/
theorem isCompletelyFaithfullyFlat_principal_of_regular (a : R) (ha : IsSMulRegular R a)
    (M : Type u) [AddCommGroup M] [Module R M] (hM : IsSMulRegular M a)
    (hFlat : Module.FaithfullyFlat (R ⧸ Ideal.span {a}) ((R ⧸ Ideal.span {a}) ⊗[R] M)) :
    IsCompletelyFaithfullyFlat (Ideal.span {a}) M := by
  have := hFlat
  exact ⟨isCompletelyFlat_principal_of_regular a ha M hM inferInstance, hFlat⟩

end SerrePositivity
