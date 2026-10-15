module

public import SerrePositivity.HomotopicalAlgebra.Transfer.EvaluationFamily
public import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-! # Cofibrations and left properness detected by evaluations

Cocontinuous evaluations carry generated cofibrations to cofibrations if
they do so on generators. A levelwise weak-equivalence class then inherits
left properness from the base model. Neither result assumes a model structure
on the evaluated category.
-/

@[expose] public section
universe w t v u v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
namespace SerrePositivity.ModelGeneration
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {D : Type u'} [Category.{v'} D]

lemma cofibrationCells_le : Quillen.relativeCells.{w} (cofibrations C) ≤
    cofibrations C := by
  have : (cofibrations C).IsStableUnderCoproducts.{w} := {}
  have : (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  exact (MorphismProperty.transfiniteCompositions_monotone
    ((MorphismProperty.pushouts_monotone (cofibrations C).coproducts_le).trans
      (cofibrations C).pushouts_le)).trans
        (cofibrations C).transfiniteCompositions_le

lemma generatedCofibrations_map_le (R : D ⥤ C) (I : MorphismProperty D)
    [I.HasSmallObjectArgument.{w}] [PreservesColimitsOfSize.{w, w} R]
    [PreservesColimitsOfShape WalkingSpan R]
    (hI : I ≤ (cofibrations C).inverseImage R) :
    I.rlp.llp ≤ (cofibrations C).inverseImage R := by
  apply generatedLeft_le_of_cells_le I ((cofibrations C).inverseImage R)
  exact (relativeCells_map_le R I (cofibrations C) hI).trans
    (fun _ _ _ hf ↦ cofibrationCells_le _ hf)

namespace EvaluationFamily
variable {ι : Type t} (R : ι → D ⥤ C)
  [∀ i, PreservesColimitsOfShape WalkingSpan (R i)]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

lemma detected_leftProper (P : MorphismProperty D)
    (hP : P ≤ detected R (cofibrations C)) :
    (detected R (weakEquivalences C)).IsStableUnderCobaseChangeAgainst P where
  isStableUnderCobaseChangeAlong {_X _Y} f hf := ⟨by
    intro Z T g l r s hg i
    have := MorphismProperty.IsStableUnderCobaseChangeAgainst.isStableUnderCobaseChangeAlong
      (P := weakEquivalences C) ((R i).map f) (hP _ hf i)
    exact MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPushout
      (P := weakEquivalences C) (s.map (R i)) (hg i)⟩

end EvaluationFamily
end SerrePositivity.ModelGeneration
