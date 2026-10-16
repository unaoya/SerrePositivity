import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero

universe v u vH uH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.SimplicialModel

-- General component detection needs no simplicial model structure or Kan source.
example (X : SSet.{v}) (T : Type v) :
    (X ⟶ PiZeroConstant.discrete T) ≃ (SSet.π₀ X → T) := PiZeroConstant.homEquiv

example (T : Type v) : SSet.KanComplex (PiZeroConstant.discrete T) :=
  PiZeroConstant.discrete_kan T

example {X Y : SSet.{v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    Function.Bijective (SSet.mapπ₀ f) := PiZeroLocalization.piZero_bijective f hf

section Source
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

example (R : OrdinaryResolutionPairs.Index (C := C))
    {f g : (OrdinaryResolutionPairs.raw.obj R).obj (Opposite.op (SimplexCategory.mk 0))}
    (h : OrdinaryMappingClassLabel.label Q R _ f = OrdinaryMappingClassLabel.label Q R _ g) :
    (OrdinaryResolutionPairs.raw.obj R).Edge f g :=
  OrdinaryRawLabelHomotopy.edgeOfLabelEq Q R h

-- Only this original small value universe has a model; u and v are independent.
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

example (R : OrdinaryResolutionPairs.Index (C := C)) :
    Function.Bijective (SSet.mapπ₀ (OrdinaryBarMappingClasses.entry R)) :=
  OrdinaryBarPiZero.entry_piZero_bijective hcof hfib R

example (b : Cᵒᵖ × C) :
    Function.Bijective (OrdinaryBarMappingClasses.piZeroLabel Q b) :=
  OrdinaryBarPiZero.piZeroLabel_bijective hcof hfib Q b

example (b : Cᵒᵖ × C) : SSet.π₀ (OrdinaryResolutionBar.functor.obj b) ≃
    (Q.obj b.1.unop ⟶ Q.obj b.2) := OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b

example (b : Cᵒᵖ × C) : Small.{v} (SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :=
  OrdinaryBarPiZero.piZero_small hcof hfib Q b

example (R : OrdinaryResolutionPairs.Index (C := C))
    (f : (OrdinaryResolutionPairs.raw.obj R).obj (Opposite.op (SimplexCategory.mk 0))) :
    OrdinaryBarPiZero.piZeroEquiv hcof hfib Q _
        (SSet.π₀.mk ((OrdinaryBarMappingClasses.entry R).app _ ⟨f⟩)) =
      (OrdinaryMappingClassLabel.sourceIso Q R (SimplexCategory.mk 0)).inv ≫ Q.map f ≫
        (OrdinaryMappingClassLabel.targetIso Q R (SimplexCategory.mk 0)).inv :=
  OrdinaryBarPiZero.piZeroEquiv_mk hcof hfib Q R f

example {b c : Cᵒᵖ × C} (f : b ⟶ c)
    (z : SSet.π₀ (OrdinaryResolutionBar.functor.obj b)) :
    OrdinaryBarPiZero.piZeroEquiv hcof hfib Q c
        (SSet.mapπ₀ (OrdinaryResolutionBar.functor.map f) z) =
      Q.map f.1.unop ≫ OrdinaryBarPiZero.piZeroEquiv hcof hfib Q b z ≫ Q.map f.2 :=
  OrdinaryBarPiZero.piZeroEquiv_naturality hcof hfib Q f z
end Source

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroConstant,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryRawLabelHomotopy,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarPiZero]
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
    throwError "Missing ordinary bar component modules"
  logInfo m!"Ordinary bar component audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
