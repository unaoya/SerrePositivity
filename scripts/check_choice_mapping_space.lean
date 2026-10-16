import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- Labels can vary across the whole parameter; neither a model nor a Kan hypothesis is supplied.
example {I : Type w} (F : I → SSet.{w})
    (hF : ∀ i, (MorphismProperty.monomorphisms SSet.{w}).rlp (terminal.from (F i)))
    {U V : SSet.{w}} (j : U ⟶ V) [Mono j]
    (a : U ⟶ DiscreteFamily.total F) (b : V ⟶ PiZeroConstant.discrete I)
    (hw : a ≫ DiscreteFamily.projection F = j ≫ b) :
    ∃ l : V ⟶ DiscreteFamily.total F, j ≫ l = a ∧ l ≫ DiscreteFamily.projection F = b :=
  DiscreteFamily.exists_extension F hF j a b hw

example {I : Type w} (F : I → SSet.{w}) (i : I) :
    DiscreteFiber.obj (DiscreteFamily.projection F) i ≅ F i :=
  DiscreteFamily.fiberIso F i

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open OrdinaryBarChoiceMappingSpace

-- The native spaces are constructed from all degrees of the actual choice categories.
example (a b : Cᵒᵖ × C) :
    space hcof hfib a b ≅ DiscreteFamily.total (fibers hcof hfib a b) := totalIso hcof hfib a b

example (a b : Cᵒᵖ × C) :
    (MorphismProperty.monomorphisms SSet.{max u v}).rlp (projection hcof hfib a b) :=
  projection_mono_rlp hcof hfib a b

example (a b : Cᵒᵖ × C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (projection hcof hfib a b)) :=
  projection_localized_isIso hcof hfib a b

example (a b : Cᵒᵖ × C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (space hcof hfib a b)) := kan hcof hfib a b

-- All unit and associativity equations are strict SSet map equalities on the auxiliary spaces.
example (a b c d : Cᵒᵖ × C) :
    composition hcof hfib a b c ▷ space hcof hfib c d ≫ composition hcof hfib a c d =
      (α_ (space hcof hfib a b) (space hcof hfib b c) (space hcof hfib c d)).hom ≫
        space hcof hfib a b ◁ composition hcof hfib b c d ≫ composition hcof hfib a b d :=
  associativity hcof hfib a b c d

example (a b : Cᵒᵖ × C) :
    identity hcof hfib a ▷ space hcof hfib a b ≫ composition hcof hfib a a b =
      (λ_ (space hcof hfib a b)).hom := left_unit hcof hfib a b

example (a b : Cᵒᵖ × C) :
    space hcof hfib a b ◁ identity hcof hfib b ≫ composition hcof hfib a b b =
      (ρ_ (space hcof hfib a b)).hom := right_unit hcof hfib a b

example (a b c : Cᵒᵖ × C) :
    composition hcof hfib a b c ≫ projection hcof hfib a c =
      (projection hcof hfib a b ⊗ₘ projection hcof hfib b c) ≫ baseComposition a b c :=
  projection_composition hcof hfib a b c

example (a : Cᵒᵖ × C) :
    identity hcof hfib a ≫ projection hcof hfib a a = baseIdentity a :=
  projection_identity hcof hfib a
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteFiber,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteFamily,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.DiscreteFamilyLifting,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarChoiceMappingSpace]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Missing choice mapping space modules"
  logInfo m!"Choice mapping space audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
