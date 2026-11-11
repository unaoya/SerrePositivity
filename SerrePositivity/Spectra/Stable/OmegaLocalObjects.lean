module

public import SerrePositivity.Spectra.Stable.OmegaDetection
public import SerrePositivity.Spectra.ModelCategory.LevelFacts

/-! # A small actual stabilization class with exactly the Omega local objects

Combinatoriality of C constructs the detecting family. The source model on
spectra only supplies its actual level classes and specified factorizations.
The output uses the original ordinary RMap local-fibrant predicate and the
independently defined level-fibrant Omega predicate.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [ModelCategory C]
  [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsLocallyPresentable.{w} C]
  (K : C) [IsCofibrant K] (I J : MorphismProperty C)
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  (hW : weakEquivalences (GeneralSymmetricSpectrum C K) =
    SpectrumLevelModel.levelProperty K (weakEquivalences C))
  (hF : fibrations (GeneralSymmetricSpectrum C K) =
    SpectrumLevelModel.levelProperty K (fibrations C))
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include I J hW hF IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
lemma exists_omega_localizingMaps :
    ∃ (ι : Type w) (G : ι → C), (∀ i, IsCofibrant (G i)) ∧
      (localizingMaps K G).IsSmall.{w} ∧
      (∀ {X Y : GeneralSymmetricSpectrum C K} (f : X ⟶ Y),
        localizingMaps K G f → IsCofibrant X ∧ IsCofibrant Y) ∧
      ∀ E : GeneralSymmetricSpectrum C K,
        Bousfield.localFibrantObjects cofSp fibSp (localizingMaps K G) E ↔
          IsFibrantOmegaSpectrum E := by
  obtain ⟨ι, G, hc, hd⟩ :=
    Bousfield.HomotopyGenerators.exists_small_cofibrant_resolution_generators
      I J IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration I J
  let cofC := MorphismProperty.functorialFactorizationData (cofibrations C) (trivialFibrations C)
  have : ∀ i, IsCofibrant (G i) := hc
  have : ∀ n : ℕ, Quillen.IsLeftQuillen (freeAt (K := K) n) := fun n ↦
    SpectrumLevelModel.freeAt_isLeftQuillen_of_level_classes K hW hF n
  refine ⟨ι, G, hc, inferInstance, localizingMaps_endpoints_cofibrant K G, ?_⟩
  intro E
  have he := SpectrumLevelModel.isFibrant_iff_levelwise K hF E
  constructor
  · intro h
    have : IsFibrant E := h.1
    exact ⟨he.mp h.1,
      (localObjects_iff_omega K cofC cofSp fibSp hcofV G (hd cofC) E).mp h.2⟩
  · intro h
    have : IsFibrant E := he.mpr h.1
    exact ⟨inferInstance,
      (localObjects_iff_omega K cofC cofSp fibSp hcofV G (hd cofC) E).mpr h.2⟩

end SerrePositivity.SpectrumStabilization
