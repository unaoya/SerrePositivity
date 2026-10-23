import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarUnitCoherence
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
open OrdinaryBarUnitTriangles OrdinaryBarUnitCoherence
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y : D C}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (cX : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X X)
  (cY : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Y)
  (c : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)

local notation "sX" => small hcof hfib X
local notation "sY" => small hcof hfib Y

-- The old chosen composition interval is retained, not replaced by another representative.
example : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ left hcof hfib P j f cX c =
    (nativeCompositionComparison hcof hfib P j (identityWord (T := T) X) f cX c c).h :=
  left_first hcof hfib P j f cX c
example : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ left hcof hfib P j f cX c =
    lift (nativeUnitComparison hcof hfib P X j cX).h
      (fst T HomotopyBinarySquare.interval ≫ nativeFamily hcof hfib P j
        (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c) ≫
          MonoidalClosed.comp sX sX sY :=
  left_second hcof hfib P j f cX c
example : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ left hcof hfib P j f cX c =
    fst T HomotopyBinarySquare.interval ≫ nativeFamily hcof hfib P j
      (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c :=
  left_constant hcof hfib P j f cX c
example : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ right hcof hfib P j f cY c =
    (nativeCompositionComparison hcof hfib P j f (identityWord (T := T) Y) c cY c).h :=
  right_first hcof hfib P j f cY c
example : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ right hcof hfib P j f cY c =
    lift (fst T HomotopyBinarySquare.interval ≫ nativeFamily hcof hfib P j
      (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c)
      (nativeUnitComparison hcof hfib P Y j cY).h ≫ MonoidalClosed.comp sX sY sY :=
  right_second hcof hfib P j f cY c
example : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ right hcof hfib P j f cY c =
    fst T HomotopyBinarySquare.interval ≫ nativeFamily hcof hfib P j
      (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C X Y) c :=
  right_constant hcof hfib P j f cY c

-- The whole original selected triangle remains a face of the higher filler.
example : SSet.stdSimplex.δ (2 : Fin 4) ≫ (leftData hcof hfib P j f cX c).tetrahedron =
    (compositionTriangle hcof hfib P j (identityWord (T := T) X) f cX c c).triangle :=
  left_retains_triangle hcof hfib P j f cX c
example : SSet.stdSimplex.δ (2 : Fin 4) ≫ (rightData hcof hfib P j f cY c).tetrahedron =
    (compositionTriangle hcof hfib P j f (identityWord (T := T) Y) c cY c).triangle :=
  right_retains_triangle hcof hfib P j f cY c

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarUnitTriangles,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarUnitCoherence]
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
  unless modules.size == expected.size do throwError "Missing native unit coherence modules"
  logInfo m!"Native unit coherence audit passed: {count} declarations in {modules.size} modules."
