import SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterUnits
import Lean.Util.CollectAxioms

universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel KanComparisonTriangle

-- Specified opposite comparisons and the constant edge bound one actual triangle.
example {T K : SSet.{v}} {f g z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (a : Data F G) (b : Data G F)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    ∃ q : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K,
      T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ q = (comparison F G a).h ∧
      T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ q = (comparison G F b).h ∧
      T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ q = fst T HomotopyBinarySquare.interval ≫ f :=
  ⟨ComparisonTriangleDegeneracy.family F G a b hK,
    ComparisonTriangleDegeneracy.family_first F G a b hK,
    ComparisonTriangleDegeneracy.family_second F G a b hK,
    ComparisonTriangleDegeneracy.family_constant F G a b hK⟩

-- No model instance or Kan assumption is needed for either binary triangle.
example {T A B K : SSet.{v}} {f₀ f₁ : T ⟶ A} {g₀ g₁ : T ⟶ B}
    (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (k : A ⊗ B ⟶ K) :
    (comparison _ _ (BinaryIntervalTriangles.lower F G k)).h =
      lift F.h (fst T HomotopyBinarySquare.interval ≫ g₀) ≫ k :=
  BinaryIntervalTriangles.lower_comparison F G k
example {T A B K : SSet.{v}} {f₀ f₁ : T ⟶ A} {g₀ g₁ : T ⟶ B}
    (F : SSet.Homotopy f₀ f₁) (G : SSet.Homotopy g₀ g₁) (k : A ⊗ B ⟶ K) :
    (comparison _ _ (BinaryIntervalTriangles.upper F G k)).h =
      lift (fst T HomotopyBinarySquare.interval ≫ f₀) G.h ≫ k :=
  BinaryIntervalTriangles.upper_comparison F G k
example {T X Y : SSet.{v}} {f₀ f₁ : T ⟶ (ihom X).obj Y} (F : SSet.Homotopy f₀ f₁) :
    (BinaryIntervalTriangles.firstFixed F (MonoidalClosed.comp X X Y)
      (f₁ := toUnit T ≫ MonoidalClosed.id X)).h = F.h :=
  ClosedParameterUnits.firstFixed_interval F

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleDegeneracy,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.BinaryIntervalTriangles,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.ClosedParameterUnits]
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
  unless modules.size == expected.size do throwError "Missing comparison unit triangle modules"
  logInfo m!"Comparison unit triangle audit passed: {count} declarations in {modules.size} modules."
