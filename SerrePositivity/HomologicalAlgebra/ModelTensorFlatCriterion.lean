module

public import SerrePositivity.HomologicalAlgebra.DerivedFlatModelTensor
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Criterion

/-! # Tensor tests on a fixed model detect actual derived purity and flat H0 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- All coefficient tests on any projective model imply purity and flatness
of the original actual homology module. -/
theorem derived_pure_flat_of_modelTensor_tests
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (P : BoundedAboveDerivedModel X.obj)
    (hAll : ∀ N : ModuleCat.{u} R, ∀ i : ℤ, i ≠ 0 →
      IsZero (((moduleTensorCochainFunctor P.complex).obj N).homology i)) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      Module.Flat R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj) := by
  have hX (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X.obj) := by
    have hk := ((homologyFunctor (ModuleCat R) (.up ℤ) i).mapIso
      (moduleTensorCochainUnitIso P.complex)).isZero_iff.mp (hAll (ModuleCat.of R R) i hi)
    exact hk.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso P.iso.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P.complex)
  let hGE : X.obj.IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr
    (fun i hi ↦ hX i (by omega))
  let hLE : X.obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr
    (fun i hi ↦ hX i (by omega))
  refine ⟨hGE, hLE, ?_⟩
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj
  let e : X ≅ boundedAboveDerivedSingleFunctor.obj H :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso X.obj 0)
  apply flat_of_completelyFlat_nilpotent (⊥ : Ideal R) ⟨1, by simp⟩ H
  intro N _ _ _
  apply (isConcentratedInDegreeZero_derivedTensor_iff H N).mpr
  intro n hn
  let N0 := ModuleCat.of R N
  let et := DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensor.mapIso
    (Iso.prod (Iso.refl (boundedAboveDerivedSingleFunctor.obj N0)) e))
  let em := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ))).mapIso
      (derivedTensorUnresolvedModuleModelIso N0 X P) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-(n : ℤ))).app
      ((moduleTensorCochainFunctor P.complex).obj N0)
  have htX := (hAll N0 (-(n : ℤ)) (by omega)).of_iso em
  have htH :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(n : ℤ))).mapIso et).isZero_iff.mp htX
  have hz := ((boundedAboveDerivedTensorModuleTorNatIso N0 n).app H).isZero_iff.mp htH
  have := ModuleCat.subsingleton_of_isZero hz
  exact (torModuleComm (R := R) n H N).injective.subsingleton

end SerrePositivity
