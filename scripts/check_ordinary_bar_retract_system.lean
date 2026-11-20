import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRetractSystem

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- The general relative space needs only a Kan target, not a contractible target or a model.
example {A B K : SSet.{w}} (i : A ⟶ B) [Mono i]
    (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (f : A ⟶ K) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from (RelativeChoiceSpace.obj i f)) :=
  LocalizedRelativeChoice.boundary_rlp i hi hK f

example {A B K : SSet.{w}} (i : A ⟶ B) [Mono i]
    (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (f : A ⟶ K) :
    i ≫ LocalizedRelativeChoice.extension i hi hK f = f :=
  LocalizedRelativeChoice.extension_fac i hi hK f

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (b : Cᵒᵖ × C) : OrdinaryBarRetractSystem.section_ hcof hfib b ≫
    OrdinaryBarRetractSystem.projection hcof hfib b = 𝟙 _ :=
  OrdinaryBarRetractSystem.section_fac hcof hfib b

example (b : Cᵒᵖ × C) : (OrdinaryBarRetractSystem.contraction hcof hfib b).h ≫
    OrdinaryBarRetractSystem.projection hcof hfib b =
      fst (OrdinaryBarRetractSystem.ambient hcof hfib b)
          (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        OrdinaryBarRetractSystem.projection hcof hfib b :=
  OrdinaryBarRetractSystem.contraction_over hcof hfib b

example {b c : Cᵒᵖ × C} (f : b ⟶ c) :
    (MorphismProperty.monomorphisms SSet.{max u v}).rlp
      (terminal.from (OrdinaryBarRetractSystem.choices hcof hfib f)) :=
  OrdinaryBarRetractSystem.choices_mono_rlp hcof hfib f

example {b c d : Cᵒᵖ × C} (f : b ⟶ c) (g : c ⟶ d) :
    OrdinaryBarRetractSystem.unit hcof hfib b ≫
        (OrdinaryBarRetractSystem.action hcof hfib f ≫
          OrdinaryBarRetractSystem.action hcof hfib g) =
      OrdinaryBarRetractSystem.boundary hcof hfib (f ≫ g) :=
  OrdinaryBarRetractSystem.composite_fac hcof hfib f g

example (b : Cᵒᵖ × C) : OrdinaryBarRetractSystem.transferFamily hcof hfib (𝟙 b)
    (OrdinaryBarRetractSystem.identityPoint hcof hfib b) =
      fst (OrdinaryBarRetractSystem.lifted hcof hfib b)
        (SSet.stdSimplex.obj (SimplexCategory.mk 0)) :=
  OrdinaryBarRetractSystem.transfer_identityPoint hcof hfib b

-- The entire prescribed large parameter is kept after transfer to a lifted small Hom.
example {b c : Cᵒᵖ × C} (f : b ⟶ c) {T U : SSet.{max u v}}
    (j : T ⟶ U) [Mono j] (s : T ⟶ OrdinaryBarRetractSystem.choices hcof hfib f) :
    ∃ t : U ⟶ OrdinaryBarRetractSystem.choices hcof hfib f, j ≫ t = s ∧
      j ≫ OrdinaryBarRetractSystem.transferred hcof hfib f t =
        OrdinaryBarRetractSystem.transferred hcof hfib f s :=
  OrdinaryBarRetractSystem.parameter_extension hcof hfib f j s

example {b c d : Cᵒᵖ × C} (f : b ⟶ c) (g : c ⟶ d) : SSet.Homotopy
    (UniverseLift.lower (OrdinaryBarRetractSystem.section_ hcof hfib b ≫
      OrdinaryBarRetractSystem.action hcof hfib f ≫ OrdinaryBarRetractSystem.action hcof hfib g ≫
        OrdinaryBarRetractSystem.projection hcof hfib d))
    (OrdinaryBarRetractSystem.smallArrow hcof hfib f ≫
      OrdinaryBarRetractSystem.smallArrow hcof hfib g) :=
  OrdinaryBarRetractSystem.smallCompositionHomotopy hcof hfib f g
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LocalizedRelativeChoice,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRetractSystem]
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
    throwError "Missing ordinary bar retract-system modules"
  logInfo m!"Ordinary bar retract-system audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
