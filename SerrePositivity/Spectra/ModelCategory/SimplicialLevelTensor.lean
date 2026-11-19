module

public import SerrePositivity.Spectra.ModelCategory.FreePushoutProductModel
public import SerrePositivity.HomotopicalAlgebra.Monoidal.GeneratedBifunctor
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleUnit

/-! # The full pushout-product axiom on the simplicial spectrum level model

Free-level generator tests are proved by the sum-degree free comparison.
The double orthogonality criterion extends them to arbitrary cofibrations.
No monoidal compatibility of spectra is an input.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
namespace SerrePositivity.SimplicialModelInputs
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

lemma simplicialLevelTensor_isQuillen :
    let := simplicialLevelModelCategory hCof hFib
    IsQuillenBifunctor (curriedTensor SymmetricSpectrum.{u}) := by
  let := simplicialLevelModelCategory hCof hFib
  let := simplicialLevelModelCategory_generated hCof hFib
  let : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} :=
    pointedSimplicial_cofibrantlyGenerated hCof hFib
  have hI {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) (hf : pointedI f) : Cofibration f := by
    apply (cofibration_iff _).2
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated pointedI pointedJ]
    exact pointedI.le_llp_rlp _ hf
  have hJ {A B : PointedSimplicialSet.{u}} (f : A ⟶ B) (hf : pointedJ f) :
      trivialCofibrations PointedSimplicialSet.{u} f := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated pointedI pointedJ]
    exact pointedJ.le_llp_rlp _ hf
  let adj := MonoidalClosed.internalHomAdjunction₂ (C := SymmetricSpectrum.{u})
  let adjFlip := SerrePositivity.ParametrizedAdjunctionTransport.left adj
    (BraidedCategory.curriedBraidingNatIso SymmetricSpectrum.{u})
  apply isQuillenBifunctor_of_generators adj adjFlip
    simplicialLevelI simplicialLevelJ simplicialLevelI simplicialLevelJ
  · intro A B i hi X Y j hj sq
    change (⨆ m : ℕ, pointedI.strictMap (SymmetricSpectrum.freeAt m)) i at hi
    change (⨆ n : ℕ, pointedI.strictMap (SymmetricSpectrum.freeAt n)) j at hj
    rw [MorphismProperty.iSup_iff] at hi hj
    obtain ⟨m, hi⟩ := hi
    obtain ⟨n, hj⟩ := hj
    cases hi with
    | map hi =>
      cases hj with
      | map hj =>
        have := hI _ hi
        have := hI _ hj
        exact freePushoutProduct_cofibration hCof hFib m n _ _ sq
  · intro A B i hi X Y j hj sq
    change (⨆ m : ℕ, pointedJ.strictMap (SymmetricSpectrum.freeAt m)) i at hi
    change (⨆ n : ℕ, pointedI.strictMap (SymmetricSpectrum.freeAt n)) j at hj
    rw [MorphismProperty.iSup_iff] at hi hj
    obtain ⟨m, hi⟩ := hi
    obtain ⟨n, hj⟩ := hj
    cases hi with
    | map hi =>
      cases hj with
      | map hj =>
        obtain ⟨hiC, hiW⟩ := (mem_trivialCofibrations_iff _).1 (hJ _ hi)
        have := hiC
        have := hI _ hj
        exact freePushoutProduct_trivialCofibration hCof hFib m n _ _ (Or.inl hiW) sq
  · intro A B i hi X Y j hj sq
    change (⨆ m : ℕ, pointedI.strictMap (SymmetricSpectrum.freeAt m)) i at hi
    change (⨆ n : ℕ, pointedJ.strictMap (SymmetricSpectrum.freeAt n)) j at hj
    rw [MorphismProperty.iSup_iff] at hi hj
    obtain ⟨m, hi⟩ := hi
    obtain ⟨n, hj⟩ := hj
    cases hi with
    | map hi =>
      cases hj with
      | map hj =>
        have := hI _ hi
        obtain ⟨hjC, hjW⟩ := (mem_trivialCofibrations_iff _).1 (hJ _ hj)
        have := hjC
        exact freePushoutProduct_trivialCofibration hCof hFib m n _ _ (Or.inr hjW) sq

lemma simplicialLevelTensor_SM7 :
    let := simplicialLevelModelCategory hCof hFib
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SymmetricSpectrum.{u})) := by
  let := simplicialLevelModelCategory hCof hFib
  exact (isQuillenBifunctor_iff_pullbackHom
    (MonoidalClosed.internalHomAdjunction₂ (C := SymmetricSpectrum.{u}))).1
      (simplicialLevelTensor_isQuillen hCof hFib)

lemma simplicialLevelTensor_unit_isCofibrant :
    let := simplicialLevelModelCategory hCof hFib
    IsCofibrant (𝟙_ SymmetricSpectrum.{u}) := by
  let := simplicialLevelModelCategory hCof hFib
  let L := SymmetricSpectrum.freeAt.{u} 0
  let : L.IsLeftAdjoint := (SymmetricSpectrum.freeAtAdjunction 0).isLeftAdjoint
  let : IsCofibrant (𝟙_ PointedSimplicialSet.{u}) := pointedSimplicial_isCofibrant hCof _
  have hfree : IsCofibrant (L.obj (𝟙_ PointedSimplicialSet.{u})) := by
    apply (isCofibrant_iff_of_isInitial
      (L.map (CategoryTheory.Limits.initial.to (𝟙_ PointedSimplicialSet.{u})))
      (CategoryTheory.Limits.initialIsInitial.isInitialObj L _)).2
    exact (cofibration_iff _).2
      ((simplicialLevel_freeAt_isLeftQuillen hCof hFib 0).map_cofibrations _
        (mem_cofibrations _))
  let : IsCofibrant (L.obj (𝟙_ PointedSimplicialSet.{u})) := hfree
  let e : L.obj (𝟙_ PointedSimplicialSet.{u}) ≅ 𝟙_ SymmetricSpectrum.{u} :=
    SymmetricSequence.freeZeroModuleUnitIso PointedSimplicialSet.sphereSequence.{u}
  exact isCofibrant_of_cofibration e.hom

lemma simplicialLevelTensor_monoidalModel :
    let := simplicialLevelModelCategory hCof hFib
    MonoidalModelCategory SymmetricSpectrum.{u} := by
  let := simplicialLevelModelCategory hCof hFib
  exact ⟨simplicialLevelTensor_isQuillen hCof hFib,
    @unitAxiom_of_cofibrant_unit SymmetricSpectrum.{u} _ _ _
      (simplicialLevelTensor_unit_isCofibrant hCof hFib)⟩

end SerrePositivity.SimplicialModelInputs
