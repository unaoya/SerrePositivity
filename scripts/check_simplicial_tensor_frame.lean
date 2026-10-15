import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorAugmentation
import Lean.Util.CollectAxioms

noncomputable section
universe v u w
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.Quillen

-- The geometric assertion is proved with no simplicial model input or citation.
example {n m : SimplexCategory} (f : n ⟶ m) :
    SerrePositivity.SimplicialHomotopy.weakEquivalences (SSet.stdSimplex.{v}.map f) :=
  SerrePositivity.SimplicialHomotopy.stdSimplex_map_weakEquivalence f

-- All based cubical loops, with arbitrary coordinate universe, contract relative
-- to the full boundary. This verifies the actual homotopy group definition.
example {X : Type u} [TopologicalSpace X] {x : X}
    (H : SerrePositivity.TopologicalHomotopy.BasedContraction x) {N : Type w}
    (p : GenLoop N X x) : GenLoop.Homotopic p GenLoop.const :=
  SerrePositivity.TopologicalHomotopy.loop_homotopic_const H p

variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory SSet.{v} C]
  (S : SerrePositivity.Enriched.TensorCotensor SSet.{v} C)

-- The augmentation is an actual natural transformation in both indexing variables.
example : tensorCosimplicialFamily S ⟶ Functor.const SimplexCategory := tensorAugmentation S
example : S.tensor.obj (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)) ≅ 𝟭 C :=
  simplexZeroTensorIso S

example [ModelCategory C] [ModelCategory SSet.{v}] [IsQuillenBifunctor S.tensor]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hw : weakEquivalences SSet.{v} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
    (X : C) [IsCofibrant X] (n : SimplexCategory) :
    weakEquivalences C (((tensorAugmentation S).app X).app n) :=
  tensorAugmentation_weakEquivalence S hcof hw X n

example [ModelCategory C] [ModelCategory SSet.{v}] [IsQuillenBifunctor S.tensor]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hw : weakEquivalences SSet.{v} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
    (X : C) [IsCofibrant X] {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C (((tensorCosimplicialFamily S).obj X).map f) :=
  tensorCosimplicial_homotopicallyConstant hcof hw S X f

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Topological.BasedContraction,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexWeakEquivalence,
    `SerrePositivity.CategoryTheory.Enriched.TensorUnit,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorConstant,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SimplicialTensorAugmentation]
  let mut count : Nat := 0
  let mut seen : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless seen.contains mod do seen := seen.push mod
  for mod in expected do
    unless seen.contains mod do throwError "Module not audited: {mod}"
  logInfo m!"Simplicial tensor frame audit passed: {count} declarations in {seen.size} modules."
