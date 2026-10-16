module

public import SerrePositivity.HomologicalAlgebra.ModelTensorFlatCriterion
public import SerrePositivity.HomologicalAlgebra.ScalarExtensionTensorCancellation

/-! # Test actual scalar extension using coefficients with their original restricted action -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Restricted coefficient tests on the original model detect purity and flat H0
of the actual scalar extension. No flatness or surjectivity of φ is needed. -/
theorem derivedBaseChange_pure_flat_of_tensor_tests
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hAll : ∀ N : ModuleCat.{u} S, ∀ i : ℤ, i ≠ 0 →
      IsZero (((moduleTensorCochainFunctor (boundedAboveDerivedChosenModel X).complex).obj
        ((ModuleCat.restrictScalars φ).obj N)).homology i)) :
    ((boundedAboveDerivedBaseChange φ).obj X).obj.IsGE 0 ∧
      ((boundedAboveDerivedBaseChange φ).obj X).obj.IsLE 0 ∧
      Module.Flat S ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) 0).obj
        ((boundedAboveDerivedBaseChange φ).obj X).obj) := by
  apply derived_pure_flat_of_modelTensor_tests
    ((boundedAboveDerivedBaseChange φ).obj X) (boundedAboveDerivedBaseChangeModel φ X)
  intro N i hi
  let P := (boundedAboveDerivedChosenModel X).complex
  let G := ModuleCat.restrictScalars.{u} φ
  let L := (moduleTensorCochainFunctor (baseChange φ P)).obj N
  let ec : (G.mapHomologicalComplex (.up ℤ)).obj L ≅
      (moduleTensorCochainFunctor P).obj (G.obj N) :=
    (Functor.mapHomologicalComplexCompIso (scalarExtensionTensorCancelIso φ N) (.up ℤ)).app P
  let eh : G.obj (L.homology i) ≅ ((moduleTensorCochainFunctor P).obj (G.obj N)).homology i :=
    (L.sc i |>.mapHomologyIso G).symm ≪≫
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso ec
  have hz := eh.isZero_iff.mpr (hAll N i hi)
  have hs : Subsingleton (G.obj (L.homology i)) := ModuleCat.isZero_iff_subsingleton.mp hz
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

end SerrePositivity
