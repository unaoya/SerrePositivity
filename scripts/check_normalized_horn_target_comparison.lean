import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetComparison
import Lean.Util.CollectAxioms

universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

-- No Kan condition on E or B and no model structure is required here.
example {E B X Y : SSet.{v}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{v}).rlp p)
    (i : X ⟶ Y) [Mono i] (f g : Y ⟶ E)
    (hfg : f ≫ p = g ≫ p) (hi : i ≫ f = i ≫ g) :
    ∃ H : SSet.Homotopy f g,
      H.h ≫ p = fst Y (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f ≫ p ∧
      i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h =
        fst X (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ i ≫ f :=
  MonoRightLiftingRelativeHomotopy.exists_relative_vertical_homotopy p hp i f g hfg hi

-- Arbitrary dimension, target map, and parameter; no model instance on SSet.
variable {K L T U : SSet.{v}} {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  (hL : SSet.modelCategoryQuillen.J.rlp (terminal.from L)) (q : K ⟶ L)

open NormalizedHornTargetComparison

example : SSet.Homotopy (sourceThenMap i hK q) (mapThenTarget i hL q) :=
  comparison i hK hL q

example (b : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) :
    SSet.Homotopy (b ≫ NormalizedHornFilling.section_ K i hK ≫
        (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map q)
      (b ≫ (ihom (SSet.horn (n + 1) i).toSSet).map q ≫
        NormalizedHornFilling.section_ L i hL) := by
  simpa only [Category.assoc] using family i hK hL q b

example (b : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) :
    (family i hK hL q b).h ≫ KanHornFamilyLifting.restriction L i =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ b ≫
        (ihom (SSet.horn (n + 1) i).toSSet).map q :=
  family_horn i hK hL q b

example (b : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) (j : U ⟶ T) :
    (family i hK hL q (j ≫ b)).h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (family i hK hL q b).h :=
  family_reindex i hK hL q b j

example (b : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) (j : U ⟶ T) :
    evaluation i hK hL q (j ≫ b) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁
        (j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ evaluation i hK hL q b :=
  evaluation_reindex i hK hL q b j

-- Every degeneracy is fixed for the whole interval, including parameter families.
example (d : Fin (n + 1))
    (e : T ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K) :
    (family i hK hL q (e ≫ DegenerateHornInput.boundary i d K)).h =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ e ≫
        DegenerateHornInput.degeneracy d K ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map q :=
  family_degenerate i hK hL q d e

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.CompatibleInputUnion,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetComparison]
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
  logInfo m!"Normalized horn target comparison audit passed: \
    {count} declarations in {modules.size} modules."
