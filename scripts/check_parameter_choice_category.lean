import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory

universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex

-- The shared-parameter target category and all its substitutions need no model structure.
example (T : SSet.{w}) : Category.{w} (ParameterCategory.Object T) := inferInstance

example {T U V : SSet.{w}} (j : U ⟶ T) (k : V ⟶ U) :
    ParameterCategory.reindex (k ≫ j) =
      ParameterCategory.reindex j ⋙ ParameterCategory.reindex k :=
  ParameterCategory.reindex_comp j k

section Actual
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (T : SSet.{max u v}) :
    Category.{max u v} (OrdinaryBarChoiceCategory.Object (C := C) hcof hfib T) := inferInstance

-- Projection is full, and does not assert faithful projection or a functorial section.
example (T : SSet.{max u v}) :
    (OrdinaryBarChoiceCategory.projection (C := C) hcof hfib T).Full :=
  OrdinaryBarChoiceCategory.projection_full hcof hfib T

-- Every mono parameter restriction extends the whole specified morphism over its same base arrow.
example {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j]
    (X Y : OrdinaryBarChoiceCategory.Object (C := C) hcof hfib T)
    (f : (OrdinaryBarChoiceCategory.reindex hcof hfib j).obj X ⟶
      (OrdinaryBarChoiceCategory.reindex hcof hfib j).obj Y) :
    ∃ g : X ⟶ Y, (OrdinaryBarChoiceCategory.reindex hcof hfib j).map g = f :=
  OrdinaryBarChoiceCategory.reindex_map_surjective hcof hfib j X Y f

example {T U V : SSet.{max u v}} (j : U ⟶ T) (k : V ⟶ U) :
    OrdinaryBarChoiceCategory.reindex (C := C) hcof hfib (k ≫ j) =
      OrdinaryBarChoiceCategory.reindex hcof hfib j ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib k :=
  OrdinaryBarChoiceCategory.reindex_comp hcof hfib j k

-- Both squares are equalities of actual functors, retaining arbitrary whole parameters.
example {T U : SSet.{max u v}} (j : U ⟶ T) :
    OrdinaryBarChoiceCategory.reindex (C := C) hcof hfib j ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib U =
      OrdinaryBarChoiceCategory.projection hcof hfib T :=
  OrdinaryBarChoiceCategory.reindex_projection hcof hfib j

example {T U : SSet.{max u v}} (j : U ⟶ T) :
    OrdinaryBarChoiceCategory.reindex (C := C) hcof hfib j ⋙
        OrdinaryBarChoiceCategory.evaluation hcof hfib U =
      OrdinaryBarChoiceCategory.evaluation hcof hfib T ⋙ ParameterCategory.reindex j :=
  OrdinaryBarChoiceCategory.reindex_evaluation hcof hfib j

-- All standard simplex operators, including degeneracies, form an actual strict diagram in Cat.
example : SimplexCategoryᵒᵖ ⥤ Cat.{max u v, u} :=
  OrdinaryBarChoiceSimplicialCategory.functor (C := C) hcof hfib

example {n m k : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (φ : m ⟶ k) :
    (OrdinaryBarChoiceSimplicialCategory.functor (C := C) hcof hfib).map (θ ≫ φ) =
      (OrdinaryBarChoiceSimplicialCategory.functor (C := C) hcof hfib).map θ ≫
        (OrdinaryBarChoiceSimplicialCategory.functor (C := C) hcof hfib).map φ :=
  (OrdinaryBarChoiceSimplicialCategory.functor hcof hfib).map_comp θ φ
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterCategory,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceCategory,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceSimplicialCategory]
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
    throwError "Missing parameter choice category modules"
  logInfo m!"Parameter choice category audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
