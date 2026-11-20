import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SimplicialModel

-- Whole interval associativity without a value model or Kan hypotheses.
example {W X Y Z T : SSet.{v}} {f₀ f₁ : T ⟶ (ihom W).obj X}
    {g₀ g₁ : T ⟶ (ihom X).obj Y} {h₀ h₁ : T ⟶ (ihom Y).obj Z}
    (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (H : SSet.Homotopy h₀ h₁) :
    (ClosedHomotopyComposition.comp (ClosedHomotopyComposition.comp F G) H).h =
      (ClosedHomotopyComposition.comp F (ClosedHomotopyComposition.comp G H)).h :=
  ClosedHomotopyComposition.assoc_interval F G H

open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P X Y)
  (d : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P Y Z)
  (e : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarRelativeHomDescent.choices hcof hfib P X Z)

example : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    OrdinaryBarRelativeHomDescent.compositionTriangleFamily hcof hfib P j f g c d e =
      (OrdinaryBarRelativeHomDescent.nativeRestrictionComparison hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e).h :=
  OrdinaryBarRelativeHomDescent.compositionTriangle_one hcof hfib P j f g c d e
example : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    OrdinaryBarRelativeHomDescent.compositionTriangleFamily hcof hfib P j f g c d e =
      (OrdinaryBarRelativeHomDescent.compositionComparison hcof hfib P j f g c d).h :=
  OrdinaryBarRelativeHomDescent.compositionTriangle_zero hcof hfib P j f g c d e
example : SSet.Homotopy
    (OrdinaryBarRelativeHomDescent.nativeFamily hcof hfib P j
      (lift (f ≫ smallAugmentation C X Y) (g ≫ smallAugmentation C Y Z) ≫
        baseComposition C X Y Z) e)
    (lift (OrdinaryBarRelativeHomDescent.nativeFamily hcof hfib P j
        (f ≫ smallAugmentation C X Y) c)
      (OrdinaryBarRelativeHomDescent.nativeFamily hcof hfib P j
        (g ≫ smallAugmentation C Y Z) d) ≫
      MonoidalClosed.comp (small hcof hfib X) (small hcof hfib Y) (small hcof hfib Z)) :=
  OrdinaryBarRelativeHomDescent.nativeCompositionComparison_base hcof hfib P j f g c d e

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyBinarySquare,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedHomotopyComposition,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTriangle,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeComposition,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle]
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
  unless modules.size == expected.size do throwError "Missing selected composition modules"
  logInfo m!"Selected composition comparison audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
