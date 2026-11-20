import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits

universe v u vE uE
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- General unit/absorption laws need only a strong contraction, not a model category.
section General
open RetractChainFamily RetractChainUnits
variable {ι : Type uE} (E K : ι → SSet.{vE}) (s : ∀ i, K i ⟶ E i) (p : ∀ i, E i ⟶ K i)
  (H : ∀ i, SSet.Homotopy (𝟙 (E i)) (p i ≫ s i))
  (hP : ∀ i, (H i).h ≫ p i = CartesianMonoidalCategory.fst (E i) interval ≫ p i)
  (hS : ∀ i, s i ▷ interval ≫ (H i).h = CartesianMonoidalCategory.fst (K i) interval ≫ s i)
  {T : SSet.{vE}}
example (i : ι) (t : T ⟶ interval) :
    ParameterComposition.comp (contraction E K s p H i t) (contraction E K s p H i (one T)) =
      contraction E K s p H i (one T) := contraction_one_right E K s p H hP i t
example (i : ι) (t : T ⟶ interval) :
    ParameterComposition.comp (contraction E K s p H i (one T)) (contraction E K s p H i t) =
      contraction E K s p H i (one T) := contraction_one_left E K s p H hS i t
example {a b : ι} (q : Chain E T a b) (t : T ⟶ interval) :
    transfer E K s p H (q.familySnoc (ParameterComposition.const T (𝟙 (E b))) t) =
      transfer E K s p H q := trailing_identity E K s p H hP q t
example {a b : ι} (q : Chain E T a b) (t : T ⟶ interval) :
    transfer E K s p H
      (((Chain.nil : Chain E T a a).familySnoc
        (ParameterComposition.const T (𝟙 (E a))) t).append q) = transfer E K s p H q :=
  leading_identity E K s p H hS q t
end General

section Actual
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarFreeChainTransfer OrdinaryBarFreeChainUnits
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {U : SSet.{max u v}} (j : U ⟶ parameters P n)
example {a : D C} {X : degree (D C) (n + 1)} (q : chain hcof hfib U a X)
    (t : U ⟶ RetractChainFamily.interval) :
    OrdinaryBarChainFamily.family hcof hfib
      (snoc hcof hfib P n j q (FreeGeneratorCategories.identity (D C) (n + 1) X) t) =
      OrdinaryBarChainFamily.family hcof hfib q := trailing_identity hcof hfib P n j q t
example {b : D C} {X : degree (D C) (n + 1)} (q : chain hcof hfib U X b)
    (t : U ⟶ RetractChainFamily.interval) :
    OrdinaryBarChainFamily.family hcof hfib
      ((snoc hcof hfib P n j (.nil : chain hcof hfib U X X)
        (FreeGeneratorCategories.identity (D C) (n + 1) X) t).append q) =
      OrdinaryBarChainFamily.family hcof hfib q := leading_identity hcof hfib P n j q t
example (X : D C) (t : U ⟶ RetractChainFamily.interval) :
    ParameterComposition.comp (parameterContraction hcof hfib X t)
      (parameterContraction hcof hfib X (RetractChainFamily.one U)) =
        parameterContraction hcof hfib X (RetractChainFamily.one U) :=
  parameterContraction_one_right hcof hfib X t
example {T : SSet.{v}} (k : UniverseLift.obj.{max u v} T ⟶ parameters P n)
    {a : D C} {X : degree (D C) (n + 1)}
    (q : chain hcof hfib (UniverseLift.obj.{max u v} T) a X)
    (t : UniverseLift.obj.{max u v} T ⟶ RetractChainFamily.interval) :
    OrdinaryBarChainFamily.smallFamily hcof hfib
      (snoc hcof hfib P n k q (FreeGeneratorCategories.identity (D C) (n + 1) X) t) =
      OrdinaryBarChainFamily.smallFamily hcof hfib q := small_trailing_identity hcof hfib P n k q t
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[`SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainUnits,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeChainUnits]
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
    throwError "Missing retract-chain unit modules"
  logInfo m!"Free chain unit audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
