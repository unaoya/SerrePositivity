import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceComposition

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- The universal property works for every parameter object, without a model or Kan hypothesis.
example {A B K T : SSet.{w}} (i : A ⟶ B) (f : A ⟶ K) :
    (T ⟶ RelativeChoiceSpace.obj i f) ≃
      {h : B ⊗ T ⟶ K // i ▷ T ≫ h = ParameterComposition.const T f} :=
  RelativeChoiceSpace.familyEquiv i f

-- A localized mono and a Kan target supply the entire fixed-boundary homotopy.
example {A B K : SSet.{w}} (i : A ⟶ B) [Mono i]
    (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (f : A ⟶ K)
    (e₀ e₁ : B ⟶ K) (h₀ : i ≫ e₀ = f) (h₁ : i ≫ e₁ = f) :
    Nonempty (RelativeChoiceSpace.FixedBoundaryHomotopy i f e₀ e₁) :=
  LocalizedRelativeChoice.nonempty_fixedBoundaryHomotopy i hi hK f e₀ e₁ h₀ h₁

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
open OrdinaryBarRetractSystem

example {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) :
    choices hcof hfib f ⊗ choices hcof hfib g ⟶ choices hcof hfib (f ≫ g) :=
  OrdinaryBarChoiceComposition.composition hcof hfib f g

-- The equality holds in the actual fiber, with the base equality transported explicitly.
example {a b c d : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
    {T : SSet.{max u v}} (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g)
    (r : T ⟶ choices hcof hfib h) :
    OrdinaryBarChoiceComposition.compose hcof hfib (f ≫ g) h
        (OrdinaryBarChoiceComposition.compose hcof hfib f g s t) r ≫
        OrdinaryBarChoiceComposition.relabel hcof hfib (Category.assoc f g h) =
      OrdinaryBarChoiceComposition.compose hcof hfib f (g ≫ h) s
        (OrdinaryBarChoiceComposition.compose hcof hfib g h t r) :=
  OrdinaryBarChoiceComposition.associativity hcof hfib f g h s t r

example {a b : Cᵒᵖ × C} (f : a ⟶ b) {T : SSet.{max u v}}
    (s : T ⟶ choices hcof hfib f) :
    OrdinaryBarChoiceComposition.compose hcof hfib (𝟙 a) f
        (OrdinaryBarChoiceComposition.identity hcof hfib a T) s ≫
        OrdinaryBarChoiceComposition.relabel hcof hfib (Category.id_comp f) = s :=
  OrdinaryBarChoiceComposition.left_unit hcof hfib f s

example {a b : Cᵒᵖ × C} (f : a ⟶ b) {T : SSet.{max u v}}
    (s : T ⟶ choices hcof hfib f) :
    OrdinaryBarChoiceComposition.compose hcof hfib f (𝟙 b) s
        (OrdinaryBarChoiceComposition.identity hcof hfib b T) ≫
        OrdinaryBarChoiceComposition.relabel hcof hfib (Category.comp_id f) = s :=
  OrdinaryBarChoiceComposition.right_unit hcof hfib f s

-- Naturality retains the entire parameter family, including arbitrary boundary restrictions.
example {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) {T U : SSet.{max u v}}
    (j : U ⟶ T) (s : T ⟶ choices hcof hfib f) (t : T ⟶ choices hcof hfib g) :
    OrdinaryBarChoiceComposition.compose hcof hfib f g (j ≫ s) (j ≫ t) =
      j ≫ OrdinaryBarChoiceComposition.compose hcof hfib f g s t :=
  OrdinaryBarChoiceComposition.compose_naturality hcof hfib f g j s t

example {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) :
    OrdinaryBarChoiceComposition.compose hcof hfib f g
        (actionPoint hcof hfib f) (actionPoint hcof hfib g) = compositePoint hcof hfib f g :=
  OrdinaryBarChoiceComposition.compose_actionPoint hcof hfib f g

-- This compares the selected composite action to the actual composite while fixing the boundary.
example {a b c : Cᵒᵖ × C} (f : a ⟶ b) (g : b ⟶ c) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (unit hcof hfib a)
      (boundary hcof hfib (f ≫ g)) (action hcof hfib (f ≫ g))
      (action hcof hfib f ≫ action hcof hfib g) :=
  OrdinaryBarChoiceComposition.compositeComparison hcof hfib f g
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceFamilies,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LocalizedRelativeChoice,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceComposition]
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
    throwError "Missing relative choice composition modules"
  logInfo m!"Relative choice composition audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
