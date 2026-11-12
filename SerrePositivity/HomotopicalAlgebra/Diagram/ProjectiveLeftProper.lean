module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveCofibrations
public import SerrePositivity.HomotopicalAlgebra.Quillen.LeftProper

/-! # Left properness of the actual projective diagram model

Projective cofibrations are objectwise cofibrations, and evaluation
preserves actual pushouts. Original left properness therefore suffices.
No left properness of a localized model is assumed.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.Projective
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

lemma leftProper :
    let := modelCategory K I J
    (weakEquivalences (K ⥤ C)).IsStableUnderCobaseChangeAgainst (cofibrations (K ⥤ C)) := by
  let := modelCategory K I J
  constructor
  intro A B f hf
  constructor
  intro Z W f' g' g sq hg k
  exact Quillen.weakEquivalence_of_pushout_along_cofibration
    (sq.map ((CategoryTheory.evaluation K C).obj k))
    (cofibrations_le_objectwise K I J f hf k) (hg k)

end SerrePositivity.DiagramModel.Projective
