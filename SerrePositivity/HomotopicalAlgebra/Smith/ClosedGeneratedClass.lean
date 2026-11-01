module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import SerrePositivity.HomotopicalAlgebra.Smith.CoproductClosure

/-! # Small generated lifting classes inside a closed class

No accessibility of the ambient morphism class is required. Only the
chosen small generating family needs the small-object argument.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C] (G P : MorphismProperty C)

lemma generatedLeft_le_of_closed [G.HasSmallObjectArgument.{w}]
    [P.IsStableUnderRetracts] [P.IsStableUnderCoproducts.{w}]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{w}]
    (hG : G ≤ P) : G.rlp.llp ≤ P := by
  apply ModelGeneration.generatedLeft_le_of_cells_le G P
  apply le_trans (MorphismProperty.transfiniteCompositions_monotone ?_) P.transfiniteCompositions_le
  apply le_trans (MorphismProperty.pushouts_monotone ?_) P.pushouts_le
  exact (MorphismProperty.coproducts_monotone hG).trans P.coproducts_le

end SerrePositivity.Smith
