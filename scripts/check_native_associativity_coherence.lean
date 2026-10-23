import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option maxHeartbeats 0
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem OrdinaryBarRelativeHomDescent
open OrdinaryBarTripleComparison OrdinaryBarAssociativityCoherence
variable {C : Type u} [Category.{v} C] {W X Y Z : D C}
variable [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}}
  (j : UniverseLift.obj.{max u v} T ⟶ P)
  (f : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C W X)
  (g : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (h : UniverseLift.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c₀₁ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P W X)
  (c₁₂ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (c₂₃ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (c₀₂ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P W Y)
  (c₁₃ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P X Z)
  (c₀₃ : UniverseLift.obj.{max u v} T ⟶ choices hcof hfib P W Z)

local notation "R" => nativeRestrictionComparison hcof hfib P j
local notation "N" => OrdinaryBarDiagonalClosedAction.nativeFamily hcof hfib P j
local notation "D" => nativeFamily hcof hfib P j
local notation "sW" => small hcof hfib W
local notation "sX" => small hcof hfib X
local notation "sY" => small hcof hfib Y
local notation "sZ" => small hcof hfib Z

-- The four actual old comparison edges occur in the new associativity disc.
example : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    left hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      (nativeCompositionComparison hcof hfib P j (wordComp f g) h c₀₂ c₂₃ c₀₃).h :=
  left_first hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃
example : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    left hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      lift (nativeCompositionComparison hcof hfib P j f g c₀₁ c₁₂ c₀₂).h
        (fst T HomotopyBinarySquare.interval ≫
          D (h ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C Y Z) c₂₃) ≫
            MonoidalClosed.comp sW sY sZ :=
  left_second hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃
example : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    right hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      (nativeCompositionComparison hcof hfib P j f (wordComp g h) c₀₁ c₁₃ c₀₃).h :=
  right_first hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃
example : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    right hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      lift (fst T HomotopyBinarySquare.interval ≫
        D (f ≫ OrdinaryBarDiagonalHomAugmentation.smallAugmentation C W X) c₀₁)
        (nativeCompositionComparison hcof hfib P j g h c₁₂ c₂₃ c₁₃).h ≫
          MonoidalClosed.comp sW sX sZ :=
  right_second hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃
example : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    left hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ =
      T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        right hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ :=
  common_diagonal hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃

-- The chosen three-dimensional fillers retain an entire selected cone face.
example : SSet.stdSimplex.δ (0 : Fin 4) ≫
    (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃).left.tetrahedron =
      (leftInnerTriangle hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂).triangle :=
  (data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃).left.face_zero

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarTripleComparison,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence]
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
  unless modules.size == expected.size do throwError "Missing native associativity modules"
  logInfo m!"Native associativity audit passed: {count} declarations in {modules.size} modules."
