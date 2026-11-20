import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonSquare
import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleBinary
import Lean.Util.CollectAxioms

universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel KanComparisonTriangle

-- Only horn lifting in K is required; there is no SSet model instance.
example {T K : SSet.{v}} {f g h z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h z)
    (a : Data F G) (b : Data F H) (c : Data G H)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    ∃ q : SSet.stdSimplex.obj (SimplexCategory.mk 3) ⟶ (ihom T).obj K,
      SSet.stdSimplex.δ (0 : Fin 4) ≫ q = c.triangle ∧
      SSet.stdSimplex.δ (1 : Fin 4) ≫ q = b.triangle ∧
      SSet.stdSimplex.δ (2 : Fin 4) ≫ q = a.triangle := by
  let d := KanComparisonTetrahedron.build F G H a b c hK
  exact ⟨d.tetrahedron, d.face_zero, d.face_one, d.face_two⟩

-- The missing face preserves a previously selected entire edge.
example {T K : SSet.{v}} {f g h z : T ⟶ K}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h z)
    (a : Data F G) (b : Data F H) (c : Data G H)
    (d : KanComparisonTetrahedron.Filler F G H a b c) :
    T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ KanComparisonTetrahedron.coherence F G H a b c d =
      (comparison G H c).h := KanComparisonTetrahedron.coherence_zero _ _ _ _ _ _ _

example {T K : SSet.{v}} {f₀ f₁ f₂ f₃ z : T ⟶ K}
    (F₀ : SSet.Homotopy f₀ z) (F₁ : SSet.Homotopy f₁ z)
    (F₂ : SSet.Homotopy f₂ z) (F₃ : SSet.Homotopy f₃ z)
    (a : Data F₀ F₁) (b : Data F₁ F₂) (c : Data F₀ F₃) (d : Data F₃ F₂)
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    let q := KanComparisonSquare.build F₀ F₁ F₂ F₃ a b c d hK
    T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ KanComparisonSquare.left F₀ F₁ F₂ F₃ a b c d q =
      T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ KanComparisonSquare.right F₀ F₁ F₂ F₃ a b c d q :=
  KanComparisonSquare.common_diagonal _ _ _ _ _ _ _ _ _

-- The third input is fixed at its first endpoint on the original comparison edge.
example {T A B K : SSet.{v}} {f g z : T ⟶ A} {h₀ h₁ : T ⟶ B}
    (F : SSet.Homotopy f z) (G : SSet.Homotopy g z) (H : SSet.Homotopy h₀ h₁)
    (k : A ⊗ B ⟶ K) (d : Data F G) :
    (comparison _ _ (ComparisonTriangleBinary.right F G H k d)).h =
      lift (comparison F G d).h (fst T HomotopyBinarySquare.interval ≫ h₀) ≫ k :=
  ComparisonTriangleBinary.right_comparison _ _ _ _ _

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonTetrahedron,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.KanComparisonSquare,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleBinary]
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
  unless modules.size == expected.size do throwError "Missing comparison tetrahedron modules"
  logInfo m!"Comparison tetrahedron audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
