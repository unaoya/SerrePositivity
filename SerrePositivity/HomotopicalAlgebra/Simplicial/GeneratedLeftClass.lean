module

public import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Cofibrant generation on Mathlib model categories

The auxiliary small-object universe is explicit. `HasSmallObjectArgument`
already includes smallness, required colimits and transfinite compactness via
Mathlib's cardinal criterion. This file does not assume that any arbitrary
set of generators automatically satisfies that criterion.
-/

@[expose] public section

universe w u v

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.ModelGeneration

variable {C : Type u} [Category.{v} C]

/-- The small-object factorization and orthogonality give a weak factorization
system, on the existing Mathlib morphism classes. -/
instance generatedWfs (I : MorphismProperty C) [I.HasSmallObjectArgument.{w}] :
    MorphismProperty.IsWeakFactorizationSystem I.rlp.llp I.rlp where
  rlp := I.rlp_llp_rlp
  llp := rfl

/-- Retract closure turns acyclicity of relative cell complexes into
acyclicity of the entire generated left class. -/
lemma generatedLeft_le_of_cells_le (I W : MorphismProperty C)
    [I.HasSmallObjectArgument.{w}] [W.IsStableUnderRetracts]
    (h : MorphismProperty.transfiniteCompositions.{w}
      (MorphismProperty.coproducts.{w} I).pushouts ≤ W) : I.rlp.llp ≤ W := by
  rw [I.llp_rlp_of_hasSmallObjectArgument]
  exact (MorphismProperty.retracts_monotone h).trans W.retracts_le

end SerrePositivity.ModelGeneration
