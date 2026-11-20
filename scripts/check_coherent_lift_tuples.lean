import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.VertexTuples
import Lean.Util.CollectAxioms

universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
  (cosimplicialHom cosimplicialHomMap)

section ArbitrarySource
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- The set of strict lifts stays in the Hom universe v, independently of u.
example (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) : Type v :=
  CoherentLiftTuples.StrictLift X Y f

-- Every strict lift vertex is retained by the single higher interpolation map.
example {X Y : ResolutionObject C} (g : X ⟶ Y) :
    SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.VertexTuples.simplex
        (fun _ : Fin 1 => (⟨g, rfl⟩ : CoherentLiftTuples.StrictLift X Y g.base)) ≫
        CoherentLiftTuples.interpolation hcof X Y g.base = ResolutionLiftSpace.ofLift g :=
  CoherentLiftTuples.simplex_vertex hcof X Y g.base ⟨g, rfl⟩

-- The same choice works in all dimensions and for all faces and degeneracies,
-- not merely for separately chosen interval homotopies.
example (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) (Z : C) {n m : ℕ}
    (a : Fin (n + 1) → CoherentLiftTuples.StrictLift X Y f)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    prod.map (SSet.stdSimplex.map θ) (𝟙 _) ≫ CoherentLiftTuples.action hcof hfib X Y f Z a =
      CoherentLiftTuples.action hcof hfib X Y f Z (fun i => a (θ.toOrderHom i)) :=
  CoherentLiftTuples.action_naturality hcof hfib X Y f Z a θ

-- Two triangular faces of the triple-composite tetrahedron agree on their
-- actual common edge. This checks compatibility across dimensions.
example (X Y W V : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y.base ⟶ W.base)
    (h : W.base ⟶ V.base) (Z : C) :
    prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3))) (𝟙 _) ≫
        CoherentLiftTuples.action hcof hfib X V (f ≫ g ≫ h) Z
          (fun j => CoherentLiftTuples.tripleCompositeVertices X Y W V f g h
            ((SimplexCategory.δ (0 : Fin 4)).toOrderHom j)) =
      prod.map (SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 3))) (𝟙 _) ≫
        CoherentLiftTuples.action hcof hfib X V (f ≫ g ≫ h) Z
          (fun j => CoherentLiftTuples.tripleCompositeVertices X Y W V f g h
            ((SimplexCategory.δ (1 : Fin 4)).toOrderHom j)) := by
  rw [CoherentLiftTuples.action_naturality, CoherentLiftTuples.action_naturality]
  congr 1

-- Degeneracies are normalized: all repeated strict identity vertices act
-- exactly by the comparison map, in every dimension.
example (X : ResolutionObject C) (Z : C) (n : ℕ) :
    CoherentLiftTuples.action hcof hfib X X (𝟙 X.base) Z
        (fun _ : Fin (n + 1) =>
          (⟨𝟙 X, rfl⟩ : CoherentLiftTuples.StrictLift X X (𝟙 X.base))) =
      prod.snd ≫ KanLiftAction.comparison hcof hfib X Z := by
  refine (CoherentLiftTuples.action_strict_constant hcof hfib (𝟙 X) Z n).trans ?_
  have hi : (cosimplicialHomMap (ResolutionObject.Hom.diagram (𝟙 X))).app Z = 𝟙 _ := by
    ext m x
    exact Category.id_comp x
  rw [hi, Category.id_comp]

-- Its fully composed vertex is the original triple precomposition, in
-- contravariant order, followed by the actual weak-equivalence comparison.
example (X Y W V : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y.base ⟶ W.base)
    (h : W.base ⟶ V.base) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (KanLiftAction.comparison hcof hfib X Z) ∧
      prod.map (SSet.stdSimplex.map ((SimplexCategory.mk 0).const (SimplexCategory.mk 3) 3))
          (𝟙 _) ≫ CoherentLiftTuples.tripleCompositeAction hcof hfib X Y W V f g h Z =
        prod.snd ≫ KanLiftCoherence.chosenMap W V h Z ≫ KanLiftCoherence.chosenMap Y W g Z ≫
          KanLiftCoherence.chosenMap X Y f Z ≫ KanLiftAction.comparison hcof hfib X Z :=
  ⟨KanLiftAction.comparison_weakEquivalence hcof hfib X Z,
    CoherentLiftTuples.tripleCompositeAction_last_vertex hcof hfib X Y W V f g h Z⟩

-- Every entire coherent simplex action remains natural in the target.
example (X Y : ResolutionObject C) (f : X.base ⟶ Y.base) {Z Z' : C} (h : Z ⟶ Z')
    {n : ℕ} (a : Fin (n + 1) → CoherentLiftTuples.StrictLift X Y f) :
    prod.map (𝟙 _) ((cosimplicialHom Y.resolution.obj).map h) ≫
        CoherentLiftTuples.action hcof hfib X Y f Z' a =
      CoherentLiftTuples.action hcof hfib X Y f Z a ≫
        (KanLiftAction.targetFunctor hcof hfib X).map h :=
  CoherentLiftTuples.action_target_naturality hcof hfib X Y f h a

end ArbitrarySource

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.VertexTuples,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftTuples]
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
  unless modules.size == expected.size do throwError "Some coherent lift modules were not audited"
  logInfo m!"Coherent lift tuple audit passed: {count} declarations in {modules.size} modules, \
    standard axioms only."
