import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceWeakEquivalence
import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightedLimit
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w})
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)

-- Actual diagram isomorphism, retaining independence of all three universes.
example (A : K ⥤ SimplexCategory ⥤ C) :
    YonedaWeightRealization.weightFamily K ⋙ SmallHomFrameWeights.functor K A ≅
      ConstantWeightHom.degree K A (SimplexCategory.mk 0) := SmallHomYonedaWeight.iso K A

-- The source of the existing weighted Quillen adjunction maps to the actual hocolim.
example (D : K ⥤ C) : weakEquivalences C
    (WeightedSourceComparison.comparison K I J D
      (HomotopyCones.weightComparison Kᵒᵖ IS JS)) :=
  WeightedSourceComparison.comparison_weakEquivalence K I J IS JS hcof hfib D

-- The final canonical mono/Kan instance needs no separate supplied generation assumption.
example (D : K ⥤ C) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    weakEquivalences C (WeightedSourceComparison.comparison K I J D
      (HomotopyCones.weightComparison Kᵒᵖ SSet.modelCategoryQuillen.I
        SSet.modelCategoryQuillen.J)) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  exact WeightedSourceComparison.comparison_weakEquivalence K I J
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J hcof hfib D

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Quillen.WeakAugmentation,
    `SerrePositivity.HomotopicalAlgebra.Diagram.YonedaWeightRealization,
    `SerrePositivity.HomotopicalAlgebra.Diagram.YonedaWeightQuillen,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomYonedaWeight,
    `SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceWeakEquivalence]
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
  logInfo m!"Weighted source weak equivalence audit passed: {count} declarations in {seen.size} modules."
