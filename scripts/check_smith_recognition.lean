import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.Smith

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.IsSmall.{w}] [W.HasTwoOutOfThreeProperty]
  [IsAccessibleCategory.{w} (Arrow C)]
  [IsAccessibleCategory.{w} (arrowProperty W).FullSubcategory]
  [(arrowInclusion W).IsAccessible.{w}] (hIW : I.rlp ≤ W)

-- J is constructed from W and I. The right-class equality needs no acyclicity input.
example : ∃ J : MorphismProperty C, J.IsSmall.{w} ∧ I.rlp = J.rlp ⊓ W := by
  have := locallyPresentable_hasColimits (C := C)
  have := hasSmallObjectArgument I
  let J := generatingTrivialCofibrations I W hIW
  exact ⟨J, inferInstance, rlp_eq_of_square_factor I J W
    (fun _ _ _ h ↦ (generatingTrivialCofibrations_le I W hIW _ h).1) hIW
    (generatingTrivialCofibrations_factor I W hIW)⟩

section AlgebraicCore
variable (J : MorphismProperty C) [J.HasSmallObjectArgument.{w}]
  (hJ : J ≤ I.rlp.llp)
  (hfactor : ∀ (i f : Arrow C), I i.hom → W f.hom → ∀ sq : i ⟶ f,
    ∃ g : Arrow C, J g.hom ∧ ∃ (p : i ⟶ g) (q : g ⟶ f), p ≫ q = sq)
  (hacyclic : J.rlp.llp ≤ W)

example : J.rlp.llp = I.rlp.llp ⊓ W :=
  generatedLeft_eq_of_square_factor I J W hJ hIW hfactor hacyclic

-- Explicit conditional core: the full theorem must still discharge these conditions.
example :
    letI : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
    letI : CategoryWithFibrations C := ⟨J.rlp⟩
    letI : CategoryWithWeakEquivalences C := ⟨W⟩
    ModelCategory C := by
  have := locallyPresentable_hasColimits (C := C)
  have := locallyPresentable_hasLimits (C := C)
  have : HasFiniteLimits C := hasFiniteLimits_of_hasLimitsOfSize C
  have := hasSmallObjectArgument I
  have : HasFiniteColimits C := hasFiniteColimits_of_hasColimitsOfSize C
  letI : CategoryWithCofibrations C := ⟨I.rlp.llp⟩
  letI : CategoryWithFibrations C := ⟨J.rlp⟩
  letI : CategoryWithWeakEquivalences C := ⟨W⟩
  exact modelCategoryOfSquareFactor I J W rfl rfl rfl hJ hIW hfactor hacyclic

example [ModelCategory C] (hF : fibrations C = J.rlp)
    (hW : weakEquivalences C = W) :
    (cofibrations C).HasFunctorialFactorization (trivialFibrations C) ∧
      (trivialCofibrations C).HasFunctorialFactorization (fibrations C) := by
  have := hasSmallObjectArgument I
  have := cofibrantlyGeneratedOfSquareFactor I J W hF hW hJ hIW hfactor
  exact ⟨SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_cofibration_trivialFibration I J,
    SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.hasFunctorialFactorization_trivialCofibration_fibration I J⟩

example [W.IsStableUnderRetracts]
    [(I.rlp.llp ⊓ W).IsStableUnderCoproducts.{w}]
    [(I.rlp.llp ⊓ W).IsStableUnderCobaseChange]
    [(I.rlp.llp ⊓ W).IsStableUnderTransfiniteComposition.{w}]
    (h : J ≤ I.rlp.llp ⊓ W) : J.rlp.llp ≤ I.rlp.llp ⊓ W :=
  generatedLeft_le_of_closure I J W h
end AlgebraicCore

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.modules[idx.toNat]!.module ==
        `SerrePositivity.HomotopicalAlgebra.Smith.Recognition do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "No Smith recognition declarations audited"
  logInfo m!"Smith recognition core audit passed: {count} declarations, standard axioms only."
