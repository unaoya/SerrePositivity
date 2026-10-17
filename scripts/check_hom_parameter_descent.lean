import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SimplicialModel
open HomotopyFunctionComplex OrdinaryBarFreeResolutionSeed

-- All simplex operators, independent universes, no source or large value model structure.
example (C : Type u) [Category.{v} C] (X Y : D C) :
    SplitEpi (OrdinaryBarSourceHom.augmentation C X Y) := OrdinaryBarHomSections.source C X Y
example (C : Type u) [Category.{v} C] (X Y : D C) :
    SplitEpi (OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) :=
  OrdinaryBarHomSections.small C X Y
example (C : Type u) [Category.{v} C] (X Y : D C) (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y).app n) :=
  OrdinaryBarHomSections.small_surjective C X Y n
example (C : Type u) [Category.{v} C] (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarSourceWordEmbedding.small C X Y)) :=
  OrdinaryBarSourceWordEmbedding.small_isIso C X Y

example {A B K : SSet.{v}} {a : A ⟶ B} (s : SplitEpi a)
    (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (P : SSet.{v}) (h : P ⊗ A ⟶ K) :
    Nonempty (SSet.Homotopy
      ((P ◁ a) ≫ SplitLocalizedDescent.descend (SplitLocalizedDescent.tensorSplit s P) h) h) :=
  SplitLocalizedDescent.tensor_descend_homotopy s ha P hK h

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

example (X Y : D C) : Nonempty (SSet.Homotopy
    ((P ◁ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) ≫
      OrdinaryBarClosedHomDescent.mapping hcof hfib P X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)) :=
  OrdinaryBarClosedHomDescent.restriction_homotopy hcof hfib P X Y
example {T : SSet.{v}} {X Y Z : D C} (j : UniverseLift.obj.{max u v} T ⟶ P)
    (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarDiagonalHomAugmentation.baseHom C X Y)
    (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarDiagonalHomAugmentation.baseHom C Y Z) :
    Nonempty (SSet.Homotopy
      (OrdinaryBarClosedHomDescent.nativeFamily hcof hfib P j
        (lift f g ≫ OrdinaryBarDiagonalHomAugmentation.baseComposition C X Y Z))
      (lift (OrdinaryBarClosedHomDescent.nativeFamily hcof hfib P j f)
        (OrdinaryBarClosedHomDescent.nativeFamily hcof hfib P j g) ≫
          MonoidalClosed.comp (OrdinaryBarRetractSystem.small hcof hfib X)
            (OrdinaryBarRetractSystem.small hcof hfib Y)
            (OrdinaryBarRetractSystem.small hcof hfib Z))) :=
  OrdinaryBarClosedHomDescent.native_composition_homotopy hcof hfib P j f g

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceSection,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarSourceWordEmbedding,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarHomSections,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SplitLocalizedDescent,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarClosedHomDescentLaws]
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
  unless modules.size == expected.size do throwError "Missing Hom descent modules"
  logInfo m!"Hom parameter descent audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
