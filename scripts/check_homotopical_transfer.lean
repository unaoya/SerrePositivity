import SerrePositivity.HomotopicalAlgebra.Foundations

universe w u₁ v₁ u₂ v₂

open CategoryTheory HomotopicalAlgebra SerrePositivity.ModelGeneration

section Generation

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]

example : cofibrations C = I.rlp.llp := cofibrations_eq_generated I J
example : trivialCofibrations C = J.rlp.llp := trivialCofibrations_eq_generated I J

example : (cofibrations C).HasFunctorialFactorization (trivialFibrations C) :=
  hasFunctorialFactorization_cofibration_trivialFibration I J
example : (trivialCofibrations C).HasFunctorialFactorization (fibrations C) :=
  hasFunctorialFactorization_trivialCofibration_fibration I J

end Generation

section Transfer

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D]
  [Limits.HasFiniteLimits D] [Limits.HasFiniteColimits D]
  (I J : MorphismProperty C) [CofibrantlyGenerated.{w} I J]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [(I.strictMap L).HasSmallObjectArgument.{w}]
  [(J.strictMap L).HasSmallObjectArgument.{w}]
  (hacyclic : MorphismProperty.transfiniteCompositions.{w}
    (MorphismProperty.coproducts.{w} (J.strictMap L)).pushouts ≤
      (weakEquivalences C).inverseImage R)

-- The theorem constructs the caller's Mathlib model structure; its chosen
-- classes, generating systems and Quillen adjunction can then be used together.
example : ModelCategory D := rightTransfer I J adj hacyclic

example :
    let m := rightTransfer I J adj hacyclic
    @weakEquivalences D _ m.categoryWithWeakEquivalences =
      (weakEquivalences C).inverseImage R := rfl

example :
    let m := rightTransfer I J adj hacyclic
    @fibrations D _ m.categoryWithFibrations =
      (fibrations C).inverseImage R := rfl

example :
    let m := rightTransfer I J adj hacyclic
    @cofibrations D _ m.categoryWithCofibrations = (I.strictMap L).rlp.llp := rfl

example :
    letI := rightTransfer I J adj hacyclic
    (cofibrations D).HasFunctorialFactorization (trivialFibrations D) := by
  let := rightTransfer I J adj hacyclic
  have := rightTransfer_cofibrantlyGenerated I J adj hacyclic
  exact hasFunctorialFactorization_cofibration_trivialFibration (I.strictMap L) (J.strictMap L)

example :
    letI := rightTransfer I J adj hacyclic
    (trivialCofibrations D).HasFunctorialFactorization (fibrations D) := by
  let := rightTransfer I J adj hacyclic
  have := rightTransfer_cofibrantlyGenerated I J adj hacyclic
  exact hasFunctorialFactorization_trivialCofibration_fibration (I.strictMap L) (J.strictMap L)

example :
    letI := rightTransfer I J adj hacyclic
    SerrePositivity.Quillen.IsLeftQuillen L ∧ SerrePositivity.Quillen.IsRightQuillen R :=
  ⟨rightTransfer_isLeftQuillen I J adj hacyclic, rightTransfer_isRightQuillen I J adj hacyclic⟩

end Transfer
