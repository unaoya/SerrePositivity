import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

-- An independent auxiliary value universe, without a model structure there.
variable {E B A T : SSet.{max u v}} (p : E ⟶ B)
  (hp : SSet.modelCategoryQuillen.J.rlp p)

-- Both whole edges and the prescribed base triangle survive the horn filling.
example (e₀ e₁ : SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ E)
    (b : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ B)
    (hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ e₀ = SSet.stdSimplex.δ (0 : Fin 2) ≫ e₁)
    (h₀ : e₀ ≫ p = SSet.stdSimplex.δ (0 : Fin 3) ≫ b)
    (h₁ : e₁ ≫ p = SSet.stdSimplex.δ (1 : Fin 3) ≫ b) :
    ∃ t : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ E,
      SSet.stdSimplex.δ (0 : Fin 3) ≫ t = e₀ ∧
      SSet.stdSimplex.δ (1 : Fin 3) ≫ t = e₁ ∧ t ≫ p = b :=
  KanTwoHornLift.exists_triangle p hp e₀ e₁ b hc h₀ h₁

-- Extension retains the specified endpoint, entire restricted interval, and exact base map.
example (i : A ⟶ T) [Mono i] (b : T ⟶ E) (a : A ⟶ E)
    (H : SSet.Homotopy a (i ≫ b))
    (q : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ B)
    (hb : b ≫ p = SSet.ι₁ ≫ q)
    (hH : H.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ q) :
    ∃ g : T ⟶ E, i ≫ g = a ∧ ∃ V : SSet.Homotopy g b,
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h ∧ V.h ≫ p = q :=
  KanFibrationEndpointExtension.exists_from_one p hp i b a H q hb hH

variable (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (H : SSet.Homotopy (𝟙 E) (p ≫ s))

-- A nonvertical original homotopy is corrected without assuming E or B Kan.
example : ∃ V : SSet.Homotopy (𝟙 E) (p ≫ s),
    V.h ≫ p = fst E (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ p :=
  KanFiberwiseContraction.exists_homotopy p hp s hs H

-- The result supplies lifts against all monos, not only terminal Kan targets.
example : (MorphismProperty.monomorphisms SSet.{max u v}).rlp p :=
  KanRetractionRightLifting.of_homotopy p hp s hs H

example : SSet.modelCategoryQuillen.I.rlp p :=
  KanRetractionRightLifting.boundary_rlp p hp s hs H

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanTwoHornLift,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.CurriedHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanFiberwiseContraction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanRetractionRightLifting]
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
  unless modules.size == expected.size do throwError "Missing Kan retraction lifting modules"
  logInfo m!"Kan retraction lifting audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
