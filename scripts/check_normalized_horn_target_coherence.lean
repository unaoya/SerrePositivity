import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetIdentity
import Lean.Util.CollectAxioms

universe u v
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

-- The union map keeps its value universe independent of the input index universe.
example {J : Type u} {B D : SSet.{v}} (S T : J → SSet.{v})
    (b : ∀ j, S j ⟶ B) (c : ∀ j, T j ⟶ D)
    (q : B ⟶ D) (t : ∀ j, S j ⟶ T j) (h : ∀ j, b j ≫ q = t j ≫ c j) :
    (CompatibleInputUnion.inputs S b).toSSet ⟶ (CompatibleInputUnion.inputs T c).toSSet :=
  CompatibleInputMap.map S T b c q t h

variable {K L M T U : SSet.{v}} {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))
  (hL : SSet.modelCategoryQuillen.J.rlp (terminal.from L))
  (hM : SSet.modelCategoryQuillen.J.rlp (terminal.from M)) (q : K ⟶ L) (r : L ⟶ M)

example : NormalizedHornInputMap.map i q ≫ NormalizedHornInputMap.map i r =
    NormalizedHornInputMap.map i (q ≫ r) := NormalizedHornInputMap.map_comp i q r

example : NormalizedHornInputMap.map i (𝟙 K) = 𝟙 _ :=
  NormalizedHornInputMap.map_id i

-- The three whole OLD intervals, including the composite comparison, are actual faces.
example : _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
    (NormalizedHornTargetComparison.comparison i hK hL q).h ≫
      (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map r := by
  rw [NormalizedHornTargetComposition.triangle_face]
  exact NormalizedHornTargetComposition.first_h i hK hL q r

example : _ ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
    ((ihom (SSet.horn (n + 1) i).toSSet).map q) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (NormalizedHornTargetComparison.comparison i hL hM r).h := by
  rw [NormalizedHornTargetComposition.triangle_face]
  exact NormalizedHornTargetComposition.second_h i hL hM q r

example : _ ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
    NormalizedHornTargetComposition.triangle i hK hL hM q r =
      (NormalizedHornTargetComparison.comparison i hK hM (q ≫ r)).h :=
  NormalizedHornTargetComposition.triangle_face i hK hL hM q r 1

example : NormalizedHornTargetComposition.triangle i hK hL hM q r ≫
    KanHornFamilyLifting.restriction M i =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫
      (ihom (SSet.horn (n + 1) i).toSSet).map (q ≫ r) :=
  NormalizedHornTargetComposition.triangle_base i hK hL hM q r

example (t : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) (j : U ⟶ T) :
    NormalizedHornTargetComposition.family i hK hL hM q r (j ≫ t) =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
        NormalizedHornTargetComposition.family i hK hL hM q r t :=
  NormalizedHornTargetComposition.family_reindex i hK hL hM q r t j

example (t : T ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K) (j : U ⟶ T) :
    NormalizedHornTargetComposition.evaluation i hK hL hM q r (j ≫ t) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁
        (j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫
          NormalizedHornTargetComposition.evaluation i hK hL hM q r t :=
  NormalizedHornTargetComposition.evaluation_reindex i hK hL hM q r t j

-- Every degenerate family is constant on the entire triangle, rather than only its edges.
example (d : Fin (n + 1))
    (e : T ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk n))).obj K) :
    NormalizedHornTargetComposition.family i hK hL hM q r
        (e ≫ DegenerateHornInput.boundary i d K) =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫ e ≫
        DegenerateHornInput.degeneracy d K ≫
          (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).map (q ≫ r) :=
  NormalizedHornTargetComposition.family_degenerate i hK hL hM q r d e

-- The original identity loop is retained, and both other edges are literally constant.
example : _ ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    NormalizedHornTargetIdentity.triangle K i hK =
      (NormalizedHornTargetComparison.comparison i hK hK (𝟙 K)).h := by
  rw [NormalizedHornTargetIdentity.triangle_face]
  exact NormalizedHornTargetIdentity.loop_h K i hK

example (k : Fin 3) (hk : k ≠ 2) : _ ◁ SSet.stdSimplex.δ k ≫
    NormalizedHornTargetIdentity.triangle K i hK =
      fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        NormalizedHornFilling.section_ K i hK := by
  rw [NormalizedHornTargetIdentity.triangle_face]
  fin_cases k
  · exact NormalizedHornTargetIdentity.constant_h K i hK
  · exact NormalizedHornTargetIdentity.constant_h K i hK
  · exact (hk rfl).elim

example : NormalizedHornTargetIdentity.triangle K i hK ≫
    KanHornFamilyLifting.restriction K i = fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) :=
  NormalizedHornTargetIdentity.triangle_base K i hK

example : (NormalizedHornTargetComparison.inputs (K := K) i).ι ▷
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫ NormalizedHornTargetIdentity.triangle K i hK =
    fst _ (SSet.stdSimplex.obj (SimplexCategory.mk 2)) ≫
      (NormalizedHornTargetComparison.inputs (K := K) i).ι ≫
        NormalizedHornFilling.section_ K i hK :=
  NormalizedHornTargetIdentity.triangle_relative K i hK

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.CompatibleInputMap,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornInputMap,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetComposition,
    `SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedHornTargetIdentity]
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
  logInfo m!"Normalized target coherence audit passed: \
    {count} declarations in {modules.size} modules."
