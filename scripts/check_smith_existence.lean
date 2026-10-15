import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra SerrePositivity.Smith
open SerrePositivity.ModelGeneration

-- These are exactly the mathematical inputs. In particular no model structure,
-- J, SOA, finite limits, acyclicity, or coproduct closure is assumed.
variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.IsSmall.{w}] [W.HasTwoOutOfThreeProperty]
  [W.IsStableUnderRetracts]
  [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
  [(arrowInclusion W).IsAccessible.{w}]
  [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
  [(I.rlp.llp ⊓ W).IsStableUnderTransfiniteComposition.{w}] (hIW : I.rlp ≤ W)

example :
    letI : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
    letI : CategoryWithFibrations C := ⟨(I.rlp.llp ⊓ W).rlp⟩
    letI : CategoryWithWeakEquivalences C := ⟨W⟩
    ModelCategory C := by
  letI : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
  letI : CategoryWithFibrations C := ⟨(I.rlp.llp ⊓ W).rlp⟩
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  exact modelCategoryOfSmith I W rfl rfl rfl hIW

example : ∃ J : MorphismProperty C, J.IsSmall.{w} ∧
    J.HasSmallObjectArgument.{w} ∧ J ≤ I.rlp.llp ⊓ W ∧
    J.rlp.llp = I.rlp.llp ⊓ W ∧ I.rlp = J.rlp ⊓ W ∧
    (I.rlp.llp).HasFunctorialFactorization I.rlp ∧
    (I.rlp.llp ⊓ W).HasFunctorialFactorization (I.rlp.llp ⊓ W).rlp := by
  let J := smithGenerators I W hIW
  have := hasSmallObjectArgument I
  have := hasSmallObjectArgument J
  refine ⟨J, inferInstance, inferInstance, smithGenerators_le I W hIW,
    smithGenerators_left I W hIW, smithGenerators_rlp I W hIW, inferInstance, ?_⟩
  rw [← smithGenerators_left I W hIW, MorphismProperty.rlp_llp_rlp]
  infer_instance

-- Both generator families admit one common regular cardinal for both endpoints.
example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    (∀ i : I.toSet, IsCardinalPresentable i.val.left κ ∧
      IsCardinalPresentable i.val.right κ) ∧
    (∀ j : (smithGenerators I W hIW).toSet, IsCardinalPresentable j.val.left κ ∧
      IsCardinalPresentable j.val.right κ) := by
  let a : Sum I.toSet (smithGenerators I W hIW).toSet → Arrow C :=
    Sum.elim (fun i ↦ i.val) (fun j ↦ j.val)
  obtain ⟨κ, hκ, ha⟩ := exists_common_arrow_presentability a
  exact ⟨κ, hκ, (fun i ↦ ha (.inl i)), (fun j ↦ ha (.inr j))⟩

-- Generation and both model factorizations on the model actually constructed above.
example :
    let : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
    let : CategoryWithFibrations C := ⟨(I.rlp.llp ⊓ W).rlp⟩
    let : CategoryWithWeakEquivalences C := ⟨W⟩
    let : ModelCategory C := modelCategoryOfSmith I W rfl rfl rfl hIW
    CofibrantlyGenerated.{w} I (smithGenerators I W hIW) ∧
      cofibrations C = I.rlp.llp ∧ weakEquivalences C = W ∧
      fibrations C = (I.rlp.llp ⊓ W).rlp ∧
      trivialCofibrations C = (smithGenerators I W hIW).rlp.llp ∧
      (cofibrations C).HasFunctorialFactorization (trivialFibrations C) ∧
      (trivialCofibrations C).HasFunctorialFactorization (fibrations C) := by
  let : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
  let : CategoryWithFibrations C := ⟨(I.rlp.llp ⊓ W).rlp⟩
  let : CategoryWithWeakEquivalences C := ⟨W⟩
  let : ModelCategory C := modelCategoryOfSmith I W rfl rfl rfl hIW
  have hgen := cofibrantlyGeneratedOfSmith I W rfl rfl hIW
  have := hgen
  exact ⟨hgen, rfl, rfl, rfl, trivialCofibrations_eq_generated I (smithGenerators I W hIW),
    hasFunctorialFactorization_cofibration_trivialFibration I (smithGenerators I W hIW),
    hasFunctorialFactorization_trivialCofibration_fibration I (smithGenerators I W hIW)⟩

-- The constructed J also retains the original square-factorization property.
example (i f : Arrow C) (hi : I i.hom) (hf : W f.hom) (sq : i ⟶ f) :
    ∃ g : Arrow C, smithGenerators I W hIW g.hom ∧
      ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq :=
  smithGenerators_factor I W hIW i f hi hf sq

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.Existence do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No Smith existence declarations audited"
  logInfo m!"Smith existence audit passed: {count} declarations, standard axioms only."
