module

public import SerrePositivity.Inputs.Homotopy.KanQuillen
public import SerrePositivity.Spectra.ModelCategory.SimplicialLevel
public import SerrePositivity.Spectra.ModelCategory.SimplicialLevelTensor

/-! # Applying HT-KQ to the proved simplicial level construction

This upper entry uses the single model-existence citation in `KanQuillen`.
The lower construction remains independent of all literature inputs.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory HomotopicalAlgebra
namespace SerrePositivity.Inputs.Homotopy
open SimplicialModelInputs

/-- The actual circle-based simplicial spectrum level model using HT-KQ. -/
@[instance_reducible]
def circleSpectrumLevelModel : ModelCategory SymmetricSpectrum.{u} := by
  let : ModelCategory SSet.{u} := kanQuillenModel
  exact simplicialLevelModelCategory kanQuillenModel_cofibrations kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_generated :
    let := circleSpectrumLevelModel.{u}
    ModelGeneration.CofibrantlyGenerated.{u} simplicialLevelI.{u} simplicialLevelJ.{u} := by
  let : ModelCategory SSet.{u} := kanQuillenModel
  exact simplicialLevelModelCategory_generated
    kanQuillenModel_cofibrations kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_monoidal :
    let := circleSpectrumLevelModel.{u}
    Quillen.MonoidalModelCategory SymmetricSpectrum.{u} := by
  let : ModelCategory SSet.{u} := kanQuillenModel
  exact simplicialLevelTensor_monoidalModel
    kanQuillenModel_cofibrations kanQuillenModel_fibrations

lemma circleSpectrumLevelModel_SM7 :
    let := circleSpectrumLevelModel.{u}
    Quillen.HasQuillenPullbackHom
      (MonoidalClosed.internalHom (C := SymmetricSpectrum.{u})) := by
  let : ModelCategory SSet.{u} := kanQuillenModel
  exact simplicialLevelTensor_SM7 kanQuillenModel_cofibrations kanQuillenModel_fibrations

end SerrePositivity.Inputs.Homotopy
