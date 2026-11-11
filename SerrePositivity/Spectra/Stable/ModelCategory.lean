module

public import SerrePositivity.Spectra.Stable.OmegaLocalObjects
public import SerrePositivity.Spectra.ModelCategory.Combinatorial
public import SerrePositivity.HomotopicalAlgebra.Localization.ModelExistence

/-! # The actual K-local model on general symmetric spectra

The small stabilization arrows and their Omega criterion are constructed
first. The proved general left Bousfield localization theorem then supplies
the model, its three classes and generating trivial cofibrations. Ordinary
suspension stability is a later comparison, not part of this construction.
-/

@[expose] public section
universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [ModelCategory C]
  (K : C) [levelModel : ModelCategory (GeneralSymmetricSpectrum C K)]
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (IP : MorphismProperty (GeneralSymmetricSpectrum C K)) [ModelCategory SSet.{v}]

structure StableModelPresentation where
  index : Type w
  tests : index → C
  tests_cofibrant : ∀ i, IsCofibrant (tests i)
  maps_small : (localizingMaps K tests).IsSmall.{w}
  localization : Bousfield.ModelPresentation.{w} cofSp fibSp IP (localizingMaps K tests)
  isLocalizationModel : Bousfield.IsLocalizationModel cofSp fibSp
    (localizingMaps K tests) localization.model
  fibrant_iff (E : GeneralSymmetricSpectrum C K) :
    localization.model.categoryWithFibrations.fibrations (terminal.from E) ↔
      IsFibrantOmegaSpectrum E

variable [HasLimitsOfSize.{0, 0} C] [IsLocallyPresentable.{w} C]
  [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (JP : MorphismProperty (GeneralSymmetricSpectrum C K))
  [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IP JP]
  (hW : weakEquivalences (GeneralSymmetricSpectrum C K) =
    SpectrumLevelModel.levelProperty K (weakEquivalences C))
  (hF : fibrations (GeneralSymmetricSpectrum C K) =
    SpectrumLevelModel.levelProperty K (fibrations C))
  [(weakEquivalences (GeneralSymmetricSpectrum C K)).IsStableUnderCobaseChangeAgainst
    (cofibrations (GeneralSymmetricSpectrum C K))]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{max v w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include I J JP hW hF IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
lemma exists_stableModelPresentation : Nonempty (StableModelPresentation.{w} K cofSp fibSp IP) := by
  have : IsLocallyPresentable.{w} (GeneralSymmetricSpectrum C K) :=
    SpectrumLevelModel.symmetricSpectrum_isLocallyPresentable (K := K)
  obtain ⟨ι, G, hc, hs, he, ho⟩ := exists_omega_localizingMaps K I J hW hF cofSp fibSp
    IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw
  have : (localizingMaps K G).IsSmall.{w} := hs
  obtain ⟨p⟩ := Bousfield.exists_modelPresentation cofSp fibSp IP JP IS JS hcofW hfibW hw
    hcofV hfibV hcofM hfibM (localizingMaps K G)
  have hp := p.isLocalizationModel cofSp fibSp IP JP IS JS hcofW hfibW hw
    hcofV hfibV hcofM hfibM
  refine ⟨{
    index := ι
    tests := G
    tests_cofibrant := hc
    maps_small := hs
    localization := p
    isLocalizationModel := hp
    fibrant_iff := ?_ }⟩
  intro E
  exact (hp.fibrant_iff E).trans (ho E)

omit [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K] in
include JP IS JS hcofW hfibW hcofV hfibV hcofM hfibM hw in
lemma StableModelPresentation.leftProper (p : StableModelPresentation.{w} K cofSp fibSp IP) :
    MorphismProperty.IsStableUnderCobaseChangeAgainst
      p.localization.model.categoryWithWeakEquivalences.weakEquivalences
      p.localization.model.categoryWithCofibrations.cofibrations := by
  have := SpectrumLevelModel.symmetricSpectrum_isLocallyPresentable (K := K)
  exact p.localization.leftProper cofSp fibSp IP JP IS JS hcofW hfibW hw
    hcofV hfibV hcofM hfibM

omit [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
  [(weakEquivalences (GeneralSymmetricSpectrum C K)).IsStableUnderCobaseChangeAgainst
    (cofibrations (GeneralSymmetricSpectrum C K))]
  [ModelCategory SSet.{w}] [ModelCategory SSet.{max v w}] in
lemma StableModelPresentation.exists_accessible_factorizations
    (p : StableModelPresentation.{w} K cofSp fibSp IP) :
    let := p.localization.model
    ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      Nonempty (Smith.AccessibleModelFactorizations (GeneralSymmetricSpectrum C K) κ) := by
  have := SpectrumLevelModel.symmetricSpectrum_isLocallyPresentable (K := K)
  exact p.localization.exists_accessible_factorizations cofSp fibSp IP

end SerrePositivity.SpectrumStabilization
