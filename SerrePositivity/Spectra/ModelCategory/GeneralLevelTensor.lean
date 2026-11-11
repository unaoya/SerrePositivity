module

public import SerrePositivity.Spectra.General.FreePushoutProduct
public import SerrePositivity.Spectra.ModelCategory.LevelFacts
public import SerrePositivity.HomotopicalAlgebra.Monoidal.GeneratedBifunctor
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleUnit

/-! # Pushout-product and unit axioms for general spectrum level models

The actual free tensor and pushout-product comparisons supply the generator
tests over arbitrary C,K. Orthogonality extends them to all cofibrations.
The separate unit result assumes a cofibrant base unit explicitly.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.Quillen
open SerrePositivity.ModelGeneration

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] [IsQuillenBifunctor (curriedTensor C)] (K : C)
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, IsLeftQuillen (freeAt (K := K) n)]

lemma general_freePushoutProduct_cofibration (m n : ℕ) {A B X Y : C}
    (i : A ⟶ B) (j : X ⟶ Y) [Cofibration i] [Cofibration j]
    (sp : (curriedTensor (GeneralSymmetricSpectrum C K)).PushoutObjObj
      ((freeAt (K := K) m).map i) ((freeAt (K := K) n).map j)) : Cofibration sp.ι := by
  let base := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) i j
  have hc : Cofibration base.ι :=
    IsQuillenBifunctor.cofibration i j base inferInstance inferInstance
  have hq : IsLeftQuillen (freeAt (K := K) (m + n)) := inferInstance
  have hf := hq.map_cofibrations base.ι ((cofibration_iff _).mp hc)
  exact (cofibration_iff _).mpr (((cofibrations (GeneralSymmetricSpectrum C K)).arrow_mk_iso_iff
    (freePushoutProductIso (K := K) m n i j base sp)).mpr hf)

lemma general_freePushoutProduct_trivialCofibration (m n : ℕ) {A B X Y : C}
    (i : A ⟶ B) (j : X ⟶ Y) [Cofibration i] [Cofibration j]
    (hw : WeakEquivalence i ∨ WeakEquivalence j)
    (sp : (curriedTensor (GeneralSymmetricSpectrum C K)).PushoutObjObj
      ((freeAt (K := K) m).map i) ((freeAt (K := K) n).map j)) :
    trivialCofibrations (GeneralSymmetricSpectrum C K) sp.ι := by
  let base := Functor.PushoutObjObj.ofHasPushout (curriedTensor C) i j
  have hc : Cofibration base.ι :=
    IsQuillenBifunctor.cofibration i j base inferInstance inferInstance
  have he : WeakEquivalence base.ι :=
    IsQuillenBifunctor.weakEquivalence i j base inferInstance inferInstance hw
  have hq : IsLeftQuillen (freeAt (K := K) (m + n)) := inferInstance
  have hf := hq.map_trivialCofibrations base.ι ((mem_trivialCofibrations_iff _).mpr ⟨hc, he⟩)
  exact ((trivialCofibrations (GeneralSymmetricSpectrum C K)).arrow_mk_iso_iff
    (freePushoutProductIso (K := K) m n i j base sp)).mpr hf

variable (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} (levelGenerators K I) (levelGenerators K J)]

include I J in
lemma general_levelTensor_isQuillen :
    IsQuillenBifunctor (curriedTensor (GeneralSymmetricSpectrum C K)) := by
  have hI {A B : C} (f : A ⟶ B) (hf : I f) : Cofibration f := by
    apply (cofibration_iff _).mpr
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.cofibrations_eq_generated I J]
    exact I.le_llp_rlp _ hf
  have hJ {A B : C} (f : A ⟶ B) (hf : J f) : trivialCofibrations C f := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J]
    exact J.le_llp_rlp _ hf
  let adj := MonoidalClosed.internalHomAdjunction₂ (C := GeneralSymmetricSpectrum C K)
  let adjFlip := SerrePositivity.ParametrizedAdjunctionTransport.left adj
    (BraidedCategory.curriedBraidingNatIso (GeneralSymmetricSpectrum C K))
  apply isQuillenBifunctor_of_generators adj adjFlip
    (levelGenerators K I) (levelGenerators K J) (levelGenerators K I) (levelGenerators K J)
  · intro A B i hi X Y j hj sq
    change (⨆ m : ℕ, I.strictMap (freeAt (K := K) m)) i at hi
    change (⨆ n : ℕ, I.strictMap (freeAt (K := K) n)) j at hj
    rw [MorphismProperty.iSup_iff] at hi hj
    obtain ⟨m, hi⟩ := hi
    obtain ⟨n, hj⟩ := hj
    cases hi with
    | map hi =>
      cases hj with
      | map hj =>
        have := hI _ hi
        have := hI _ hj
        exact general_freePushoutProduct_cofibration K m n _ _ sq
  · intro A B i hi X Y j hj sq
    change (⨆ m : ℕ, J.strictMap (freeAt (K := K) m)) i at hi
    change (⨆ n : ℕ, I.strictMap (freeAt (K := K) n)) j at hj
    rw [MorphismProperty.iSup_iff] at hi hj
    obtain ⟨m, hi⟩ := hi
    obtain ⟨n, hj⟩ := hj
    cases hi with
    | map hi =>
      cases hj with
      | map hj =>
        obtain ⟨hiC, hiW⟩ := (mem_trivialCofibrations_iff _).mp (hJ _ hi)
        have := hiC
        have := hI _ hj
        exact general_freePushoutProduct_trivialCofibration K m n _ _ (Or.inl hiW) sq
  · intro A B i hi X Y j hj sq
    change (⨆ m : ℕ, I.strictMap (freeAt (K := K) m)) i at hi
    change (⨆ n : ℕ, J.strictMap (freeAt (K := K) n)) j at hj
    rw [MorphismProperty.iSup_iff] at hi hj
    obtain ⟨m, hi⟩ := hi
    obtain ⟨n, hj⟩ := hj
    cases hi with
    | map hi =>
      cases hj with
      | map hj =>
        have := hI _ hi
        obtain ⟨hjC, hjW⟩ := (mem_trivialCofibrations_iff _).mp (hJ _ hj)
        have := hjC
        exact general_freePushoutProduct_trivialCofibration K m n _ _ (Or.inr hjW) sq

omit [IsQuillenBifunctor (curriedTensor C)] in
lemma general_levelUnit_isCofibrant [IsCofibrant (𝟙_ C)] :
    IsCofibrant (𝟙_ (GeneralSymmetricSpectrum C K)) := by
  have := (freeAtAdjunction (K := K) 0).isLeftAdjoint
  have := map_isCofibrant (freeAt (K := K) 0) (𝟙_ C)
  let e : (freeAt (K := K) 0).obj (𝟙_ C) ≅ 𝟙_ (GeneralSymmetricSpectrum C K) :=
    SymmetricSequence.freeZeroModuleUnitIso (SymmetricSequence.tensorPowerSequence K)
  exact isCofibrant_of_cofibration e.hom

include I J in
lemma general_levelTensor_monoidalModel [IsCofibrant (𝟙_ C)] :
    MonoidalModelCategory (GeneralSymmetricSpectrum C K) := by
  have := general_levelUnit_isCofibrant K
  exact ⟨general_levelTensor_isQuillen K I J, unitAxiom_of_cofibrant_unit _⟩

end SerrePositivity.SpectrumLevelModel
