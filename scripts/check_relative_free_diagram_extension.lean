import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension

universe v u uV vV
noncomputable section
open CategoryTheory
open HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {V : Type uV} [Quiver.{vV} V] {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j]

-- The quiver universes are independent; freeness is imposed only on the auxiliary diagram source.
example (A : Paths V ⥤ OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib U) :
    OrdinaryBarFreeDiagramExtension.extendFunctor hcof hfib j A ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib j = A :=
  OrdinaryBarFreeDiagramExtension.extendFunctor_restriction hcof hfib j A

example (A : Paths V ⥤ OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib U) :
    OrdinaryBarFreeDiagramExtension.extendFunctor hcof hfib j A ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib T =
      A ⋙ OrdinaryBarChoiceCategory.projection hcof hfib U :=
  OrdinaryBarFreeDiagramExtension.extendFunctor_projection hcof hfib j A

-- An actual lift is constructed from a base diagram alone, without lifting data as an input.
example (F : Paths V ⥤ (Cᵒᵖ × C)) (P : SSet.{max u v}) :
    OrdinaryBarFreeDiagramExtension.liftBase hcof hfib F P ⋙
      OrdinaryBarChoiceCategory.projection hcof hfib P = F :=
  OrdinaryBarFreeDiagramExtension.liftBase_projection hcof hfib F P

example (P : SSet.{max u v}) :
    OrdinaryBarFreeDiagramExtension.freeCover (C := C) hcof hfib P ⋙
        OrdinaryBarChoiceCategory.projection hcof hfib P = Paths.lift (𝟭q (Cᵒᵖ × C)) :=
  OrdinaryBarFreeDiagramExtension.freeCover_projection hcof hfib P

-- Prescribed generators are retained over all of T, and restriction still recovers all of A.
example (A : Paths V ⥤ OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib U)
    (Q : OrdinaryBarRelativeFreeDiagramExtension.Prescribed hcof hfib j
      (Paths.of V ⋙q A.toPrefunctor)) :
    OrdinaryBarRelativeFreeDiagramExtension.extendFunctor hcof hfib j A Q ⋙
        OrdinaryBarChoiceCategory.reindex hcof hfib j = A :=
  OrdinaryBarRelativeFreeDiagramExtension.extendFunctor_restriction hcof hfib j A Q

example (φ : V ⥤q OrdinaryBarFreeDiagramExtension.target (C := C) hcof hfib U)
    (Q : OrdinaryBarRelativeFreeDiagramExtension.Prescribed hcof hfib j φ)
    {X Y : V} (q : Quiver.Path X Y)
    (hq : OrdinaryBarRelativeFreeDiagramExtension.AllFixed hcof hfib j φ Q q) :
    (OrdinaryBarRelativeFreeDiagramExtension.extend hcof hfib j φ Q).map q =
      OrdinaryBarRelativeFreeDiagramExtension.prescribedPath hcof hfib j φ Q q hq :=
  OrdinaryBarRelativeFreeDiagramExtension.extend_fixed_path hcof hfib j φ Q q hq

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarFreeDiagramExtension,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarRelativeFreeDiagramExtension]
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
    throwError "Missing relative free diagram extension modules"
  logInfo m!"Relative free diagram extension audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
