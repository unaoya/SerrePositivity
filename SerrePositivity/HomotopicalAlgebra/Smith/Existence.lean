module

public import SerrePositivity.HomotopicalAlgebra.Smith.Recognition
public import SerrePositivity.HomotopicalAlgebra.Smith.Completeness
public import SerrePositivity.HomotopicalAlgebra.Smith.CoproductClosure
public import Mathlib.CategoryTheory.Presentable.Comma

/-! # Smith recognition in locally presentable categories

The generating trivial cofibrations, both small-object arguments, acyclicity,
finite limits and finite colimits are outputs of the proof. The assumptions
are accessibility of the weak equivalences, two-out-of-three and retract
closure, and cobase-change/transfinite-composition closure of the acyclic
generated cofibrations. This constructs Mathlib's existing model structure.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.IsSmall.{w}] [W.HasTwoOutOfThreeProperty]
  [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
  [(arrowInclusion W).IsAccessible.{w}]

/-- The chosen small generating trivial cofibrations, with the required I-SOA
derived internally from local presentability. -/
def smithGenerators (hIW : I.rlp ≤ W) : MorphismProperty C :=
  have := locallyPresentable_hasColimits (C := C)
  have := hasSmallObjectArgument I
  generatingTrivialCofibrations I W hIW

instance smithGenerators_isSmall (hIW : I.rlp ≤ W) :
    (smithGenerators I W hIW).IsSmall.{w} := by
  have := locallyPresentable_hasColimits (C := C)
  have := hasSmallObjectArgument I
  exact generatingTrivialCofibrations_isSmall I W hIW

lemma smithGenerators_le (hIW : I.rlp ≤ W) :
    smithGenerators I W hIW ≤ I.rlp.llp ⊓ W := by
  have := locallyPresentable_hasColimits (C := C)
  have := hasSmallObjectArgument I
  exact generatingTrivialCofibrations_le I W hIW

lemma smithGenerators_factor (hIW : I.rlp ≤ W)
    (i f : Arrow C) (hi : I i.hom) (hf : W f.hom) (sq : i ⟶ f) :
    ∃ g : Arrow C, smithGenerators I W hIW g.hom ∧
      ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq := by
  have := locallyPresentable_hasColimits (C := C)
  have := hasSmallObjectArgument I
  exact generatingTrivialCofibrations_factor I W hIW i f hi hf sq

lemma smithGenerators_rlp (hIW : I.rlp ≤ W) :
    I.rlp = (smithGenerators I W hIW).rlp ⊓ W :=
  rlp_eq_of_square_factor I _ W
    (fun _ _ _ h ↦ (smithGenerators_le I W hIW _ h).1) hIW
    (smithGenerators_factor I W hIW)

variable [W.IsStableUnderRetracts]
  [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [(I.rlp.llp ⊓ W).IsStableUnderTransfiniteComposition.{w}]

/-- Cell acyclicity is derived; coproduct closure is not an extra assumption. -/
lemma smithGenerators_acyclic (hIW : I.rlp ≤ W) :
    (smithGenerators I W hIW).rlp.llp ≤ I.rlp.llp ⊓ W := by
  have := locallyPresentable_hasColimits (C := C)
  have := hasSmallObjectArgument (smithGenerators I W hIW)
  have := MorphismClosure.stableUnderCoproducts (I.rlp.llp ⊓ W)
  exact generatedLeft_le_of_closure I _ W (smithGenerators_le I W hIW)

lemma smithGenerators_left (hIW : I.rlp ≤ W) :
    (smithGenerators I W hIW).rlp.llp = I.rlp.llp ⊓ W := by
  have := hasSmallObjectArgument (smithGenerators I W hIW)
  exact generatedLeft_eq_of_square_factor I _ W
    (fun _ _ _ h ↦ (smithGenerators_le I W hIW _ h).1) hIW
    (smithGenerators_factor I W hIW)
    (fun _ _ _ h ↦ (smithGenerators_acyclic I W hIW _ h).2)

lemma smithGenerators_fibrations (hIW : I.rlp ≤ W) :
    (I.rlp.llp ⊓ W).rlp = (smithGenerators I W hIW).rlp := by
  rw [← smithGenerators_left I W hIW, MorphismProperty.rlp_llp_rlp]

section Model
variable [CategoryWithCofibrations C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C]
  (hC : cofibrations C = I.rlp.llp)
  (hF : fibrations C = (I.rlp.llp ⊓ W).rlp)
  (hW : weakEquivalences C = W)

/-- Smith recognition with no given J, SOA, acyclicity, or finite-limit assumption.
The caller's classes are precisely generated cofibrations, W, and the right
orthogonal of their intersection. -/
@[instance_reducible]
def modelCategoryOfSmith (hIW : I.rlp ≤ W) : ModelCategory C := by
  have := locallyPresentable_hasColimits (C := C)
  have := locallyPresentable_hasLimits (C := C)
  have : HasFiniteColimits C := hasFiniteColimits_of_hasColimitsOfSize C
  have : HasFiniteLimits C := hasFiniteLimits_of_hasLimitsOfSize C
  have := hasSmallObjectArgument I
  have := hasSmallObjectArgument (smithGenerators I W hIW)
  exact modelCategoryOfSquareFactor I _ W hC
    (hF.trans (smithGenerators_fibrations I W hIW)) hW
    (fun _ _ _ h ↦ (smithGenerators_le I W hIW _ h).1) hIW
    (smithGenerators_factor I W hIW)
    (fun _ _ _ h ↦ (smithGenerators_acyclic I W hIW _ h).2)

end Model

lemma cofibrantlyGeneratedOfSmith [ModelCategory C]
    (hF : fibrations C = (I.rlp.llp ⊓ W).rlp) (hW : weakEquivalences C = W)
    (hIW : I.rlp ≤ W) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I (smithGenerators I W hIW) := by
  have := hasSmallObjectArgument I
  have := hasSmallObjectArgument (smithGenerators I W hIW)
  exact cofibrantlyGeneratedOfSquareFactor I _ W
    (hF.trans (smithGenerators_fibrations I W hIW)) hW
    (fun _ _ _ h ↦ (smithGenerators_le I W hIW _ h).1) hIW
    (smithGenerators_factor I W hIW)

end SerrePositivity.Smith
