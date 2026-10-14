module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
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

section Model

variable [ModelCategory C]

/-- Cofibrant generation is extra structure on the existing model category:
two generating classes, their small-object hypotheses, and the two right-class
equalities. It is not a replacement definition of a model category. -/
class CofibrantlyGenerated (I J : MorphismProperty C) : Prop where
  smallObjectI : I.HasSmallObjectArgument.{w}
  smallObjectJ : J.HasSmallObjectArgument.{w}
  rlp_I : I.rlp = trivialFibrations C
  rlp_J : J.rlp = fibrations C

attribute [instance] CofibrantlyGenerated.smallObjectI CofibrantlyGenerated.smallObjectJ

variable (I J : MorphismProperty C) [hgen : CofibrantlyGenerated.{w} I J]

include hgen

lemma cofibrations_eq_generated : cofibrations C = I.rlp.llp := by
  rw [CofibrantlyGenerated.rlp_I (I := I) (J := J), trivialFibrations_llp]

lemma trivialCofibrations_eq_generated : trivialCofibrations C = J.rlp.llp := by
  rw [CofibrantlyGenerated.rlp_J (I := I) (J := J), fibrations_llp]

/-- Cofibrant generation supplies the first functorial model factorization. -/
lemma hasFunctorialFactorization_cofibration_trivialFibration :
    (cofibrations C).HasFunctorialFactorization (trivialFibrations C) := by
  rw [cofibrations_eq_generated I J, ← CofibrantlyGenerated.rlp_I (I := I) (J := J)]
  infer_instance

/-- Cofibrant generation supplies the second functorial model factorization. -/
lemma hasFunctorialFactorization_trivialCofibration_fibration :
    (trivialCofibrations C).HasFunctorialFactorization (fibrations C) := by
  rw [trivialCofibrations_eq_generated I J, ← CofibrantlyGenerated.rlp_J (I := I) (J := J)]
  infer_instance

end Model

end SerrePositivity.ModelGeneration
