module

public import SerrePositivity.Spectra.ModelCategory.PointedGenerators
public import SerrePositivity.HomotopicalAlgebra.Pointed.SmashModel
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility

/-! # Shared simplicial model compatibility and its pointed applications -/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
namespace SerrePositivity.SimplicialModelInputs
open SSet SerrePositivity.Quillen

alias simplicial_pushoutProduct_mono :=
  SerrePositivity.SimplicialModel.simplicial_pushoutProduct_mono
alias simplicial_anodyne_eq_trivialCofibrations :=
  SerrePositivity.SimplicialModel.simplicial_anodyne_eq_trivialCofibrations
alias simplicial_cofibrantlyGenerated :=
  SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated
alias simplicial_isQuillenBifunctor := SerrePositivity.SimplicialModel.simplicial_isQuillenBifunctor
alias simplicial_monoidalModel := SerrePositivity.SimplicialModel.simplicial_monoidalModel
alias simplicial_SM7 := SerrePositivity.SimplicialModel.simplicial_SM7

section Model
variable [ModelCategory SSet.{u}]
  (hCof : cofibrations SSet.{u} = MorphismProperty.monomorphisms SSet.{u})
  (hFib : fibrations SSet.{u} = SSet.modelCategoryQuillen.J.{u}.rlp)

include hCof hFib in
lemma pointedSimplicial_monoidalModel : MonoidalModelCategory PointedSimplicialSet.{u} := by
  let : IsQuillenBifunctor (curriedTensor SSet.{u}) := simplicial_isQuillenBifunctor hCof hFib
  let : IsCofibrant (𝟙_ SSet.{u}) := by
    constructor
    rw [hCof]
    infer_instance
  exact SerrePositivity.PointedModel.smash_monoidalModel

include hCof hFib in
lemma pointedSimplicial_SM7 :
    HasQuillenPullbackHom (MonoidalClosed.internalHom (C := PointedSimplicialSet.{u})) := by
  let : IsQuillenBifunctor (curriedTensor SSet.{u}) := simplicial_isQuillenBifunctor hCof hFib
  exact SerrePositivity.PointedModel.smash_hasQuillenPullbackHom

include hCof in
/-- Cofibrancy for the supplied model, using its explicit monomorphism class. -/
lemma pointedSimplicial_isCofibrant (X : PointedSimplicialSet.{u}) : IsCofibrant X := by
  apply (SerrePositivity.PointedModel.isCofibrant_iff_basepoint X).2
  apply (HomotopicalAlgebra.cofibration_iff _).2
  rw [hCof]
  exact pointed_basepoint_mono X

include hCof hFib in
/-- The free pointed boundary/horn maps generate the inherited model. -/
lemma pointedSimplicial_cofibrantlyGenerated :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u} pointedI.{u} pointedJ.{u} := by
  let : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      SSet.modelCategoryQuillen.I.{u} SSet.modelCategoryQuillen.J.{u} :=
    simplicial_cofibrantlyGenerated hCof hFib
  constructor
  · exact pointedI_smallObjectArgument
  · exact pointedJ_smallObjectArgument
  · rw [pointedGenerators_rlp,
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.rlp_I
        (I := SSet.modelCategoryQuillen.I) (J := SSet.modelCategoryQuillen.J),
      trivialFibrations_under_eq, MorphismProperty.under_eq_inverseImage]
  · rw [pointedGenerators_rlp, ← hFib, fibrations_under_def,
      MorphismProperty.under_eq_inverseImage]

end Model
end SerrePositivity.SimplicialModelInputs
