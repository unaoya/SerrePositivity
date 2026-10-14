module

public import SerrePositivity.Spectra.ModelCategory.LevelRecognition
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap
public import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-! # Level-cell acyclicity from the free-level generator calculations

A relative free J-cell is trivial at every level if every evaluated free
J-generator is a trivial cofibration in C. Evaluation preserves the coproduct,
pushout and ordinal stages. Weak equivalences alone would not be enough here.
-/

@[expose] public section
universe w u v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.ModelGeneration
open SerrePositivity.Quillen

namespace SerrePositivity.SpectrumLevelModel
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{w, w} C] [ModelCategory C] (K : C)

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{w, w} C] in
lemma trivialCofibrationCells_le : relativeCells.{w} (trivialCofibrations C) ≤
    trivialCofibrations C := by
  have : (trivialCofibrations C).IsStableUnderCoproducts.{w} := {}
  have : (trivialCofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← fibrations_llp]
    infer_instance
  exact (MorphismProperty.transfiniteCompositions_monotone
    ((MorphismProperty.pushouts_monotone (trivialCofibrations C).coproducts_le).trans
      (trivialCofibrations C).pushouts_le)).trans
        (trivialCofibrations C).transfiniteCompositions_le

/-- Acyclicity reduced to computations on F_n followed by evaluation at m. -/
lemma levelCells_acyclic_of_evaluated_generators (J : MorphismProperty C)
    (h : ∀ n m : ℕ, J.strictMap (freeAt (K := K) n ⋙ evaluation m) ≤
      trivialCofibrations C) :
    relativeCells.{w} (levelGenerators K J) ≤ levelProperty K (weakEquivalences C) := by
  intro A B f hf m
  let : PreservesColimitsOfSize.{w, w} (evaluation (K := K) m) := {}
  have hg : levelGenerators K J ≤
      (trivialCofibrations C).inverseImage (evaluation (K := K) m) := by
    intro A B i hi
    change (⨆ n : ℕ, J.strictMap (freeAt (K := K) n)) i at hi
    rw [MorphismProperty.iSup_iff] at hi
    obtain ⟨n, hi⟩ := hi
    cases hi with
    | map hi => exact h n m _ (J.map_mem_strictMap _ _ hi)
  have hc := relativeCells_map_le (evaluation (K := K) m) (levelGenerators K J)
    (trivialCofibrations C) hg _ hf
  exact (trivialCofibrationCells_le _ hc).2
end SerrePositivity.SpectrumLevelModel
