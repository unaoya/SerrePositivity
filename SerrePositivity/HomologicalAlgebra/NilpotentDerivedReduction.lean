module
public import SerrePositivity.HomologicalAlgebra.DerivedFlatModelTensor
public import SerrePositivity.HomologicalAlgebra.ScalarExtensionTensorCancellation
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatNilpotent

/-! # Lift actual derived flatness across arbitrary nilpotent ideals -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (I : Ideal R)
  (X : DerivedCategory.Minus (ModuleCat.{u} R))
variable
  (hPure : ∀ j : ℤ, j ≠ 0 → IsZero
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ I)) j).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj X).obj))
  (hFlat : Module.Flat (R ⧸ I)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (R ⧸ I)) 0).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj X).obj))
include hPure hFlat

/-- The actual pure flat residue supplies tensor tests for all I-annihilated modules. -/
lemma modelTensor_homology_isZero_of_flat_reduction (N : ModuleCat.{u} R)
    (hN : ∀ r ∈ I, ∀ x : N, r • x = 0) (i : ℤ) (hi : i ≠ 0) :
    IsZero (((moduleTensorCochainFunctor
      (boundedAboveDerivedChosenModel X).complex).obj N).homology i) := by
  let φ := Ideal.Quotient.mk I
  let P := boundedAboveDerivedChosenModel X
  have hNt : Module.IsTorsionBySet R N (I : Set R) := fun {x} {r} ↦ hN r r.property x
  let := hNt.module
  let NQ := ModuleCat.of (R ⧸ I) N
  let G := ModuleCat.restrictScalars.{u} φ
  let L := (moduleTensorCochainFunctor (baseChange φ P.complex)).obj NQ
  let E : G.obj NQ ≃ₗ[R] N :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hzL : IsZero (L.homology i) :=
    moduleTensorCochain_model_homology_isZero_of_pure_flat
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj X)
      (boundedAboveDerivedBaseChangeModel φ X) hPure hFlat NQ i hi
  let ec : (G.mapHomologicalComplex (.up ℤ)).obj L ≅
      (moduleTensorCochainFunctor P.complex).obj (G.obj NQ) :=
    (Functor.mapHomologicalComplexCompIso (scalarExtensionTensorCancelIso φ NQ) (.up ℤ)).app
      P.complex
  let eh : G.obj (L.homology i) ≅
      ((moduleTensorCochainFunctor P.complex).obj (G.obj NQ)).homology i :=
    (L.sc i |>.mapHomologyIso G).symm ≪≫
      (homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso ec
  have hz := eh.isZero_iff.mp (G.map_isZero hzL)
  exact ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    ((moduleTensorCochainFunctor P.complex).mapIso E.toModuleIso)).isZero_iff.mp hz

/-- G10: a pure flat actual reduction across a nilpotent ideal makes X pure and H⁰ flat. -/
theorem derived_pure_flat_of_nilpotent_reduction (hNil : ∃ n : ℕ, I ^ n = ⊥) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      Module.Flat R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj X.obj) := by
  let P := boundedAboveDerivedChosenModel X
  have hP : ∀ j, Module.Flat R (P.complex.X j) := by
    intro j
    have : Module.Projective R (P.complex.X j) := inferInstance
    infer_instance
  have hAll (N : ModuleCat.{u} R) (i : ℤ) (hi : i ≠ 0) :
      IsZero (((moduleTensorCochainFunctor P.complex).obj N).homology i) :=
    moduleTensorCochain_homology_isZero_of_nilpotentIdeal I hNil P.complex hP i
      (fun N hN ↦ modelTensor_homology_isZero_of_flat_reduction I X hPure hFlat N hN i hi) N
  have hX (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj X.obj) := by
    have hk := cochain_homology_isZero_of_nilpotentIdeal_tests I hNil P.complex hP i
      (fun N hN ↦ modelTensor_homology_isZero_of_flat_reduction I X hPure hFlat N hN i hi)
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
  intro N _ _ hN
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
