import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonCoherenceRestriction
import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarAssociativityCoherence
import Lean.Util.CollectAxioms

universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

section Generic
open KanComparisonTriangle
variable {T U V K : SSet.{v}} (i : U ⟶ T) (k : V ⟶ U) {f₀ f₁ f₂ f₃ z : T ⟶ K}
  (F₀ : SSet.Homotopy f₀ z) (F₁ : SSet.Homotopy f₁ z)
  (F₂ : SSet.Homotopy f₂ z) (F₃ : SSet.Homotopy f₃ z)
  (a : Data F₀ F₁) (b : Data F₁ F₂) (c : Data F₀ F₃) (d : Data F₃ F₂)
  (e : KanComparisonSquare.Filler F₀ F₁ F₂ F₃ a b c d)

-- Entire three-dimensional fillers, not just the resulting comparison classes.
example : uncurry (ComparisonCoherenceRestriction.square i F₀ F₁ F₂ F₃ a b c d e).left.tetrahedron =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ uncurry e.left.tetrahedron :=
  ComparisonCoherenceRestriction.left_tetrahedron_family i F₀ F₁ F₂ F₃ a b c d e
example : (ComparisonCoherenceRestriction.square (𝟙 T) F₀ F₁ F₂ F₃ a b c d e).right.tetrahedron =
    e.right.tetrahedron :=
  ComparisonCoherenceRestriction.right_tetrahedron_identity F₀ F₁ F₂ F₃ a b c d e
example : let q := ComparisonCoherenceRestriction.square i F₀ F₁ F₂ F₃ a b c d e
    (ComparisonCoherenceRestriction.square k
      (HomotopyClasses.preHomotopy i F₀) (HomotopyClasses.preHomotopy i F₁)
      (HomotopyClasses.preHomotopy i F₂) (HomotopyClasses.preHomotopy i F₃)
      (ComparisonCoherenceRestriction.triangle i F₀ F₁ a)
      (ComparisonCoherenceRestriction.triangle i F₁ F₂ b)
      (ComparisonCoherenceRestriction.triangle i F₀ F₃ c)
      (ComparisonCoherenceRestriction.triangle i F₃ F₂ d) q).left.tetrahedron =
        (ComparisonCoherenceRestriction.square (k ≫ i) F₀ F₁ F₂ F₃ a b c d e).left.tetrahedron :=
  ComparisonCoherenceRestriction.left_tetrahedron_comp i F₀ F₁ F₂ F₃ a b c d e k
end Generic

section Native
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

local notation "F₀" => root hcof hfib P j f g h c₀₃
local notation "F₁" => leftIntermediate hcof hfib P j f g h c₂₃ c₀₂
local notation "F₂" => total hcof hfib P j f g h c₀₁ c₁₂ c₂₃
local notation "F₃" => rightIntermediate hcof hfib P j f g h c₀₁ c₁₃
local notation "a" => leftOuterTriangle hcof hfib P j f g h c₂₃ c₀₂ c₀₃
local notation "b" => leftInnerTriangle hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂
local notation "c" => rightOuterTriangle hcof hfib P j f g h c₀₁ c₁₃ c₀₃
local notation "d" => rightInnerTriangle hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₁₃

local notation "e" => data hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃
variable {U : SSet.{v}} (i : U ⟶ T)

-- The actual native disc restricts in the original small value universe.
example : KanComparisonSquare.left
    (HomotopyClasses.preHomotopy i F₀) (HomotopyClasses.preHomotopy i F₁)
    (HomotopyClasses.preHomotopy i F₂) (HomotopyClasses.preHomotopy i F₃)
    (ComparisonCoherenceRestriction.triangle i F₀ F₁ a)
    (ComparisonCoherenceRestriction.triangle i F₁ F₂ b)
    (ComparisonCoherenceRestriction.triangle i F₀ F₃ c)
    (ComparisonCoherenceRestriction.triangle i F₃ F₂ d)
    (ComparisonCoherenceRestriction.square i F₀ F₁ F₂ F₃ a b c d e) =
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
        left hcof hfib P j f g h c₀₁ c₁₂ c₂₃ c₀₂ c₁₃ c₀₃ :=
  ComparisonCoherenceRestriction.left_family i F₀ F₁ F₂ F₃ a b c d e
example :
    uncurry (ComparisonCoherenceRestriction.square i F₀ F₁ F₂ F₃ a b c d e).right.tetrahedron =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 3) ≫ uncurry (e).right.tetrahedron :=
  ComparisonCoherenceRestriction.right_tetrahedron_family i F₀ F₁ F₂ F₃ a b c d e
end Native

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonCoherenceTransport,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonCoherenceRestriction]
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
  unless modules.size == expected.size do throwError "Missing coherence transport modules"
  logInfo m!"Coherence transport audit passed: {count} declarations in {modules.size} modules."
