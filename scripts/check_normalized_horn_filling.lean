import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornFilling
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

-- The overlap theorem is categorical and dimension-independent.
example {C : Type u} [Category.{v} C] (X : CosimplicialObject C) {P : C}
    {n : ℕ} (i : Fin (n + 2)) (j k : Fin (n + 1))
    (a b : X.obj (SimplexCategory.mk n) ⟶ P)
    (h : ∀ r : Fin (n + 2), r ≠ i → X.δ r ≫ X.σ j ≫ a = X.δ r ≫ X.σ k ≫ b) :
    X.σ j ≫ a = X.σ k ≫ b := CosimplicialDegenerateHorn.eq_of_faces X i j k a b h
example (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2)) (j k : Fin (n + 1))
    {L : SSet.{v}} (a b : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K)
    (h : a ≫ DegenerateHornInput.boundary i j K = b ≫ DegenerateHornInput.boundary i k K) :
    a ≫ DegenerateHornInput.degeneracy j K = b ≫ DegenerateHornInput.degeneracy k K :=
  DegenerateHornOverlap.eq_of_same_horn K i j k a b h

section Normalized
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

-- The same chosen operation preserves all d, including the one-dimensional case n = 0.
example : NormalizedHornFilling.section_ K i hK ≫ KanHornFamilyLifting.restriction K i = 𝟙 _ :=
  NormalizedHornFilling.section_restriction K i hK
example (d : Fin (n + 1)) : DegenerateHornInput.boundary i d K ≫
    NormalizedHornFilling.section_ K i hK = DegenerateHornInput.degeneracy d K :=
  NormalizedHornFilling.section_degeneracy K i hK d
example {T : SSet.{v}} (d : Fin (n + 1))
    (e : SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ (ihom T).obj K) :
    NormalizedHornFilling.fill K i hK ((SSet.horn (n + 1) i).ι ≫ SSet.stdSimplex.σ d ≫ e) =
      SSet.stdSimplex.σ d ≫ e := NormalizedHornFilling.fill_degenerate K i hK d e
example {T U : SSet.{v}} (b : (SSet.horn (n + 1) i).toSSet ⟶ (ihom T).obj K) (j : U ⟶ T) :
    uncurry (NormalizedHornFilling.fill K i hK (b ≫ (pre j).app K)) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ≫
        uncurry (NormalizedHornFilling.fill K i hK b) :=
  NormalizedHornFilling.family_reindex K i hK b j
example {T : SSet.{v}} (b : (SSet.horn (n + 1) i).toSSet ⟶ (ihom T).obj K)
    (a : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : (SSet.horn (n + 1) i).ι ≫ a = b) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn (n + 1) i).ι b a
      (NormalizedHornFilling.fill K i hK b) :=
  NormalizedHornFilling.compare K i hK b a ha
end Normalized

-- The earlier triangle choice agrees, rather than being silently replaced.
example (K : SSet.{v}) (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) (i : Fin 3) :
    NormalizedHornFilling.section_ K i hK = NormalizedTriangleHorn.section_ K i hK :=
  NormalizedHornFilling.triangle_section K hK i

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.CosimplicialDegenerateHorn,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.DegenerateHornOverlap,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornFilling]
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
  unless modules.size == expected.size do throwError "Missing normalized horn modules"
  logInfo m!"Normalized horn audit passed: {count} declarations in {modules.size} modules."
