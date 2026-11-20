module

public import SerrePositivity.Spectra.Stable.OrdinarySuspension
public import SerrePositivity.Spectra.ModelCategory.PointedPresentability
public import SerrePositivity.Spectra.Stable.DerivedTensorInverse

/-! # Ordinary suspension stability of the constructed circle localization

The actual constructed localization supplies left properness, generation
and the pointed action. Its proved K-invertibility for K = S¹ supplies
invertibility of derived circle tensor. All derived functors are selected
from their established existence; no stable-equivalence or suspension
invertibility hypothesis is an input.
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Quillen SerrePositivity.ModelGeneration
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.SpectrumLevelModel
open SerrePositivity.SimplicialModelInputs SerrePositivity.PointedSimplicialSet

namespace SerrePositivity.SpectrumStabilization
theorem StableModelPresentation.exists_ordinarySuspensionLoopEquivalence [ModelCategory SSet.{u}]
    [original : ModelCategory (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u}))]
    [∀ n : ℕ, IsLeftQuillen (freeAt (K := (circle.{u})) n)]
    [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} (levelGenerators (circle.{u}) pointedI.{u})
      (levelGenerators (circle.{u}) pointedJ.{u})]
    [MorphismProperty.IsStableUnderCobaseChangeAgainst
      (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u})))
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u})))]
    (cofSp : MorphismProperty.FunctorialFactorizationData
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u})))
      (trivialFibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u}))))
    (fibSp : MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u})))
      (fibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u}))))
    (p : StableModelPresentation.{u} (circle.{u}) cofSp fibSp
      (levelGenerators (circle.{u}) pointedI.{u}))
    (hcof : cofibrations SSet.{u} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)
    (hw : weakEquivalences SSet.{u} = SimplicialHomotopy.weakEquivalences)
    :
    let := pointedSimplicial_isLocallyPresentable.{u}
    let G := p.localization.generators
    let hg := p.localization.generated
    let lp := symmetricSpectrum_isLocallyPresentable (K := (circle.{u}))
    let := p.localization.model
    let := hg
    let := lp
    let W := weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u}))
    ∃ (LSigma ROmega : W.Localization ⥤ W.Localization)
      (γ : W.Q ⋙ LSigma ⟶ SymmetricSpectrum.suspensionFunctor.{u} ⋙ W.Q)
      (ρ : (GeneralSymmetricSpectrum.cotensorFunctor (K := circle.{u}) circle) ⋙ W.Q ⟶ W.Q ⋙ ROmega),
      LSigma.IsLeftDerivedFunctor γ W ∧ ROmega.IsRightDerivedFunctor ρ W ∧
      ∃ e : W.Localization ≌ W.Localization,
        e.functor = HomotopySuspension.localizedFunctor
          (levelGenerators (circle.{u}) pointedI) G W.Q ∧
          e.inverse = ROmega := by
  have := pointedSimplicial_isLocallyPresentable.{u}
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} :=
    pointedSimplicial_cofibrantlyGenerated hcof hfib
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J :=
    _root_.SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  have : MonoidalModelCategory PointedSimplicialSet.{u} :=
    pointedSimplicial_monoidalModel hcof hfib
  have : IsCofibrant circle.{u} := pointedSimplicial_isCofibrant hcof _
  let : EnrichedOrdinaryCategory PointedSimplicialSet.{u}
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u})) :=
    mappingEnrichedOrdinaryCategory
  have haction := (p.enriched_model (circle.{u}) pointedI pointedJ cofSp fibSp hcof hfib
    (fun {A B} _ _ ↦ pointedSimplicial_isCofibrant hcof A)).1
  have hproper := p.leftProper (circle.{u}) cofSp fibSp
    (levelGenerators (circle.{u}) pointedI) (levelGenerators (circle.{u}) pointedJ)
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J hcof hfib hcof hfib hcof hfib hw
  have : IsCofibrant (𝟙_ PointedSimplicialSet.{u}) := pointedSimplicial_isCofibrant hcof _
  have := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration pointedI.{u} pointedJ.{u}
  let cofC := MorphismProperty.functorialFactorizationData
    (cofibrations PointedSimplicialSet.{u}) (trivialFibrations PointedSimplicialSet.{u})
  have := general_levelTensor_isQuillen (circle.{u}) pointedI pointedJ
  have hT0 := p.freeTensor_isLeftQuillen (circle.{u}) cofSp fibSp _ hcof hfib 0 (circle.{u})
  have hT1 := p.freeTensor_isLeftQuillen (circle.{u}) cofSp fibSp _ hcof hfib 1
    (𝟙_ PointedSimplicialSet.{u})
  let G := p.localization.generators
  have hg := p.localization.generated
  have lp := symmetricSpectrum_isLocallyPresentable (K := (circle.{u}))
  let stableModel := p.localization.model
  let := stableModel
  let nativeModel : ModelCategory SymmetricSpectrum.{u} := stableModel
  let := nativeModel
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} (levelGenerators (circle.{u}) pointedI) G := hg
  have : IsLocallyPresentable.{u}
      (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u})) := lp
  have : MorphismProperty.IsStableUnderCobaseChangeAgainst
      (weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u})))
      (cofibrations (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u}))) := hproper
  have : IsQuillenBifunctor (pointwiseTensorBifunctor (K := (circle.{u}))) := haction
  let W := weakEquivalences (GeneralSymmetricSpectrum PointedSimplicialSet.{u} (circle.{u}))
  have : IsLocallyPresentable.{u} SymmetricSpectrum.{u} := lp
  have : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} (C := SymmetricSpectrum.{u})
      (levelGenerators (circle.{u}) pointedI) G := hg
  have : MorphismProperty.IsStableUnderCobaseChangeAgainst
      (weakEquivalences SymmetricSpectrum.{u}) (cofibrations SymmetricSpectrum.{u}) := hproper
  have : W.Q.IsLocalization (weakEquivalences SymmetricSpectrum.{u}) :=
    inferInstanceAs (W.Q.IsLocalization W)
  have hL : IsLeftQuillen SymmetricSpectrum.suspensionFunctor.{u} :=
    circleTensor_isLeftQuillen (K := (circle.{u})) (spectrumModel := stableModel) hcof
  have hR := isRightQuillen_of_isLeftQuillen SymmetricSpectrum.suspensionLoopAdjunction.{u}
  have : Functor.HasPointwiseLeftDerivedFunctor
      (tensorLeft ((freeAt (K := (circle.{u})) 0).obj (circle.{u})) ⋙ W.Q) W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ stableModel _ _ stableModel _ _ W.Q
      inferInstance _ hT0
  have : Functor.HasPointwiseLeftDerivedFunctor
      (tensorLeft ((freeAt (K := (circle.{u})) 1).obj (𝟙_ PointedSimplicialSet.{u})) ⋙ W.Q)
      W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ stableModel _ _ stableModel _ _ W.Q
      inferInstance _ hT1
  have : (SymmetricSpectrum.suspensionFunctor.{u} ⋙ W.Q).HasPointwiseLeftDerivedFunctor W :=
    @Quillen.hasPointwiseLeftDerivedFunctor _ _ nativeModel _ _ nativeModel _ _ W.Q
      inferInstance _ hL
  have : ((GeneralSymmetricSpectrum.cotensorFunctor (K := circle.{u}) circle) ⋙
      W.Q).HasPointwiseRightDerivedFunctor W :=
    @Quillen.hasPointwiseRightDerivedFunctor _ _ nativeModel _ _ nativeModel _ _ W.Q
      inferInstance _ hR
  let α := Functor.totalLeftDerivedCounit
    (tensorLeft ((freeAt (K := (circle.{u})) 0).obj (circle.{u})) ⋙ W.Q) W.Q W
  let β := Functor.totalLeftDerivedCounit
    (tensorLeft ((freeAt (K := (circle.{u})) 1).obj (𝟙_ PointedSimplicialSet.{u})) ⋙ W.Q) W.Q W
  let γ := (SymmetricSpectrum.suspensionFunctor.{u} ⋙ W.Q).totalLeftDerivedCounit W.Q W
  let ρ := ((GeneralSymmetricSpectrum.cotensorFunctor (K := circle.{u}) circle) ⋙
    W.Q).totalRightDerivedUnit W.Q W
  have hSigma := p.derived_pointwiseTensor_isEquivalence (levelModel := original)
    (circle.{u}) pointedI pointedJ cofC cofSp fibSp hcof hfib
    (fun {A B} _ _ ↦ pointedSimplicial_isCofibrant hcof A) W.Q α β γ
    (hQ := inferInstanceAs (W.Q.IsLocalization W))
    (hα := inferInstanceAs (Functor.IsLeftDerivedFunctor
      (Functor.totalLeftDerived
        (tensorLeft ((freeAt (K := (circle.{u})) 0).obj (circle.{u})) ⋙ W.Q) W.Q W) α W))
    (hβ := inferInstanceAs (Functor.IsLeftDerivedFunctor
      (Functor.totalLeftDerived
        (tensorLeft ((freeAt (K := (circle.{u})) 1).obj (𝟙_ PointedSimplicialSet.{u})) ⋙ W.Q)
        W.Q W) β W))
    (hγ := inferInstanceAs (Functor.IsLeftDerivedFunctor
      ((SymmetricSpectrum.suspensionFunctor.{u} ⋙ W.Q).totalLeftDerived W.Q W) γ W))
  let e := SymmetricSpectrum.ordinarySuspensionLoopEquivalence
    (spectrumModel := nativeModel) (levelGenerators (circle.{u}) pointedI) G
    hcof hw W.Q γ ρ hSigma
    (hQ := inferInstanceAs (W.Q.IsLocalization W))
    (hγ := inferInstanceAs (Functor.IsLeftDerivedFunctor
      ((SymmetricSpectrum.suspensionFunctor.{u} ⋙ W.Q).totalLeftDerived W.Q W) γ W))
    (hρ := inferInstanceAs (Functor.IsRightDerivedFunctor
      (((GeneralSymmetricSpectrum.cotensorFunctor (K := circle.{u}) circle) ⋙
        W.Q).totalRightDerived W.Q W) ρ W))
  exact ⟨_, _, γ, ρ, inferInstance, inferInstance, e, rfl, rfl⟩


end SerrePositivity.SpectrumStabilization
