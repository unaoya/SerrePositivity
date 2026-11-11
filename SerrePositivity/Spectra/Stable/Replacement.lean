module

public import SerrePositivity.Spectra.Stable.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.Localization.Replacement

/-! # Actual accessible Omega replacement for the constructed spectral model

Its unit is an original cofibration and a stable equivalence. Its values are
level-fibrant Omega spectra, and the original weak equivalences of the values
detect exactly the weak equivalences of the constructed localized model.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (K : C) [levelModel : ModelCategory (GeneralSymmetricSpectrum C K)]
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (IP JP : MorphismProperty (GeneralSymmetricSpectrum C K))
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IP JP]
  [(weakEquivalences (GeneralSymmetricSpectrum C K)).IsStableUnderCobaseChangeAgainst
    (cofibrations (GeneralSymmetricSpectrum C K))]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include JP IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
lemma StableModelPresentation.exists_accessible_omegaReplacement
    (p : StableModelPresentation.{w} K cofSp fibSp IP) :
    ∃ d : Bousfield.LocalReplacementData.{v, max u v}
        (C := GeneralSymmetricSpectrum C K) cofSp fibSp (localizingMaps K p.tests),
      d.L.IsAccessible.{w} ∧ (∀ E, IsFibrantOmegaSpectrum (d.L.obj E)) ∧
      p.localization.model.categoryWithWeakEquivalences.weakEquivalences =
        (weakEquivalences (GeneralSymmetricSpectrum C K)).inverseImage d.L := by
  have := SpectrumLevelModel.symmetricSpectrum_isLocallyPresentable (K := K)
  have : (localizingMaps K p.tests).IsSmall.{w} := p.maps_small
  obtain ⟨d, hd⟩ := Bousfield.exists_accessible_localReplacementData cofSp fibSp IP JP IS JS
    hcofW hfibW hw hcofV hfibV hcofM hfibM (localizingMaps K p.tests)
  have h := p.localization.isLocalizationModel cofSp fibSp IP JP IS JS
    hcofW hfibW hw hcofV hfibV hcofM hfibM
  refine ⟨d, hd, fun E ↦ ?_, ?_⟩
  · exact (p.fibrant_iff _).mp ((h.fibrant_iff _).mpr (d.localFibrant E))
  · exact p.localization.weakEquivalences_eq.trans (d.detects_localEquivalences hcofV hfibV)

end SerrePositivity.SpectrumStabilization
