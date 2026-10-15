module

public import SerrePositivity.Spectra.Stable.UniversalLocalizingMaps
public import SerrePositivity.Spectra.General.TensorFreeAtSum
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleUnit

/-! # The actual evaluation map for a tensor inverse of F₀(K)

The map F₁(1) tensor F₀(K) -> 1 is obtained from the degree-zero
stabilization map by actual free-tensor and unit comparisons. Its local weak
equivalence is a first step toward derived invertibility, not yet a proof of
a Quillen equivalence or of ordinary suspension stability.
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
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] (K : C)

def tensorInverseEvaluation :
    (freeAt (K := K) 1).obj (𝟙_ C) ⊗ (freeAt (K := K) 0).obj K ⟶
      𝟙_ (GeneralSymmetricSpectrum C K) :=
  (tensorFreeAtSum (K := K) 1 0 (𝟙_ C) K).hom ≫ localizingMap K 0 (𝟙_ C) ≫
    (SymmetricSequence.freeZeroModuleUnitIso (SymmetricSequence.tensorPowerSequence K)).hom

variable [ModelCategory C] [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
  [IsCofibrant (𝟙_ C)] [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, Quillen.IsLeftQuillen (freeAt (K := K) n)] [ModelCategory SSet.{v}]
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (IP : MorphismProperty (GeneralSymmetricSpectrum C K))
  (p : StableModelPresentation.{w} K cofSp fibSp IP)
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include cofC hcof hfib in
lemma StableModelPresentation.tensorInverseEvaluation_isWeakEquivalence :
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences
      (tensorInverseEvaluation K) := by
  have hσ := p.localizingMap_isWeakEquivalence K cofC cofSp fibSp IP hcof hfib 0 (𝟙_ C)
  let := p.localization.model
  have : WeakEquivalence (localizingMap K 0 (𝟙_ C)) := ⟨hσ⟩
  change weakEquivalences (GeneralSymmetricSpectrum C K) _
  unfold tensorInverseEvaluation
  exact mem_weakEquivalences _

end SerrePositivity.SpectrumStabilization
