import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison

universe v u uV vV
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarFreeDiagramExtension

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

section General
variable {V : Type uV} [Quiver.{vV} V] {P : SSet.{max u v}}
  (φ : V ⥤q target (C := C) hcof hfib P)
  (ψ : OrdinaryBarFreeDiagramHomotopy.End hcof hfib φ)
  (Q : OrdinaryBarFreeDiagramHomotopy.Fixed hcof hfib φ ψ)

example : OrdinaryBarFreeDiagramHomotopy.comparison hcof hfib φ ψ Q ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ = Paths.lift φ :=
  OrdinaryBarFreeDiagramHomotopy.comparison_zero hcof hfib φ ψ Q

example : OrdinaryBarFreeDiagramHomotopy.comparison hcof hfib φ ψ Q ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ =
      Paths.lift (OrdinaryBarFreeDiagramHomotopy.endGenerators hcof hfib φ ψ) :=
  OrdinaryBarFreeDiagramHomotopy.comparison_one hcof hfib φ ψ Q

example {X Y : V} (e : X ⟶ Y) (he : Q.predicate e) :
    (OrdinaryBarFreeDiagramHomotopy.comparison hcof hfib φ ψ Q).map e.toPath =
      (OrdinaryBarChoiceCategory.reindex hcof hfib
        (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1)))).map (φ.map e) :=
  OrdinaryBarFreeDiagramHomotopy.comparison_fixed hcof hfib φ ψ Q e he
end General

-- Both endpoints are the actual first two faces of the cover of the entire original base.
section Actual
variable (P : SSet.{max u v})

example : OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₀ =
      OrdinaryBarFreeResolutionFaces.faceZero hcof hfib P :=
  OrdinaryBarFreeResolutionComparison.comparison_zero hcof hfib P

example : OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.reindex hcof hfib SSet.ι₁ =
      OrdinaryBarFreeResolutionFaces.faceOne hcof hfib P :=
  OrdinaryBarFreeResolutionComparison.comparison_one hcof hfib P

-- Equality of whole functors: every path in the degeneracy image is fixed, including units.
example : FreePathResolution.duplicate (Cᵒᵖ × C) ⋙
    OrdinaryBarFreeResolutionComparison.comparison hcof hfib P = freeCover hcof hfib P ⋙
      OrdinaryBarChoiceCategory.reindex hcof hfib
        (fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1))) :=
  OrdinaryBarFreeResolutionComparison.comparison_degeneracy hcof hfib P

example : OrdinaryBarFreeResolutionComparison.comparison (C := C) hcof hfib P ⋙
    OrdinaryBarChoiceCategory.projection hcof hfib _ =
      OrdinaryBarFreeResolutionFaces.faceZero hcof hfib P ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib P :=
  OrdinaryBarFreeResolutionComparison.comparison_projection hcof hfib P
end Actual

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramHomotopy,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeResolutionComparison]
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
    throwError "Missing relative free-resolution comparison modules"
  logInfo m!"Relative free-resolution comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
