import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe u v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

variable {A B E P : SSet.{max u v}}

-- Both orientations preserve the prescribed base interval in an independent value universe.
example {T : SSet.{max u v}} (q : E ⟶ B) (hq : SSet.modelCategoryQuillen.J.rlp q)
    (j : A ⟶ T) [Mono j] (b : T ⟶ E) (a : A ⟶ E)
    (H : SSet.Homotopy (j ≫ b) a)
    (base : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶ B)
    (hb : b ≫ q = SSet.ι₀ ≫ base)
    (hH : H.h ≫ q = j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ base) :
    ∃ g : T ⟶ E, j ≫ g = a ∧ ∃ V : SSet.Homotopy b g,
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h = H.h ∧ V.h ≫ q = base :=
  KanFibrationEndpointExtension.exists_from_zero q hq j b a H base hb hH

variable (i : A ⟶ B) (r : B ⟶ A) (hi : i ≫ r = 𝟙 A)
  (H : SSet.Homotopy (𝟙 B) (r ≫ i))
  (hfix : i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
    fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ i)
  (q : E ⟶ B) (hq : SSet.modelCategoryQuillen.J.rlp q)
  (j : P ⟶ E) (k : P ⟶ A) (sq : IsPullback j k q i)

-- No Kan condition on A, B, or E, and no value model structure is supplied.
-- The original pullback j is retained; its mono property is derived.
example : ∃ s : E ⟶ P, j ≫ s = 𝟙 P ∧ ∃ V : SSet.Homotopy (𝟙 E) (s ≫ j),
    j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ V.h =
      fst P (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ j ∧
    V.h ≫ q = q ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h :=
  KanPullbackDeformation.exists_retraction i r hi H hfix q hq j k sq

example : IsIso (AnodyneHomotopy.anodyneQ.map j) :=
  KanPullbackDeformation.localized_isIso i r hi H hfix q hq j k sq

example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) : IsIso (L.map j) :=
  KanPullbackDeformation.image_isIso i r hi H hfix q hq j k sq L hL

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.KanPullbackDeformation]
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
  unless modules.size == expected.size do throwError "Missing Kan pullback deformation modules"
  logInfo m!"Kan pullback deformation audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
