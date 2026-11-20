import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeComparisonTriangle
import Lean.Util.CollectAxioms

universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

-- Neither E nor B is assumed Kan, and no model structure is required.
variable {E B A X U V : SSet.{v}} (p : E ⟶ B)
  (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
  (i : A ⟶ X) [Mono i] (j : U ⟶ V) [Mono j]
  (earlier : X ⊗ U ⟶ E) (prescribed : A ⊗ V ⟶ E) (base : X ⊗ V ⟶ B)
  (hc : i ▷ U ≫ earlier = A ◁ j ≫ prescribed)
  (he : earlier ≫ p = X ◁ j ≫ base) (ha : prescribed ≫ p = i ▷ V ≫ base)

example : ∃ f : X ⊗ V ⟶ E,
    X ◁ j ≫ f = earlier ∧ i ▷ V ≫ f = prescribed ∧ f ≫ p = base :=
  RelativeProductLifting.exists_lift p hp i j earlier prescribed base hc he ha

-- All faces in arbitrary dimensions are retained, with strict parameter restriction.
example (a : A ⟶ E) (b : X ⟶ B) (hab : a ≫ p = i ≫ b) {n : ℕ}
    (faces : Fin (n + 3) → (X ⊗ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ E))
    (hc : BoundaryTensorGluing.Compatible faces)
    (hb : ∀ k, faces k ≫ p = fst X _ ≫ b)
    (ha : ∀ k, i ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ≫ faces k =
      fst A _ ≫ a) (k : Fin (n + 3)) :
    X ◁ SSet.stdSimplex.δ k ≫
      RelativeBoundaryFilling.filler p hp i a b hab faces hc hb ha = faces k :=
  RelativeBoundaryFilling.filler_face p hp i a b hab faces hc hb ha k

-- Three previously chosen entire intervals are literal faces of one triangle.
example {f g h : X ⟶ E} (F : SSet.Homotopy f g) (G : SSet.Homotopy g h)
    (H : SSet.Homotopy f h) (a : A ⟶ E) (b : X ⟶ B) (hab : a ≫ p = i ≫ b)
    (hF : F.h ≫ p = fst X _ ≫ b) (hG : G.h ≫ p = fst X _ ≫ b)
    (hH : H.h ≫ p = fst X _ ≫ b)
    (rF : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ F.h = fst A _ ≫ a)
    (rG : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ G.h = fst A _ ≫ a)
    (rH : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h = fst A _ ≫ a)
    (k : Fin 3) :
    X ◁ SSet.stdSimplex.δ k ≫
      RelativeComparisonTriangle.triangle F G H p hp i a b hab hF hG hH rF rG rH =
        ![G.h, H.h, F.h] k :=
  RelativeComparisonTriangle.triangle_face F G H p hp i a b hab hF hG hH rF rG rH k

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeProductLifting,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeBoundaryFilling,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeComparisonTriangle]
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
  unless modules.size == expected.size do throwError "Missing target comparison modules"
  logInfo m!"Relative boundary filling audit passed: \
    {count} declarations in {modules.size} modules."
