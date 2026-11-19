import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceComparison
import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightedLimit
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel

section Ordinary
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w, w} C] (A : K ⥤ SimplexCategory ⥤ C)

-- Actual object isomorphisms, with no model structures on C or SSet.
example (n : SimplexCategory) :
    (FrameWeightRealization.functor K A).obj (ConstantWeightHom.weight K n) ≅
      colimit (ConstantWeightHom.degree K A n) := ConstantWeightRealization.iso K A n

example : (FrameWeightRealization.functor K A).obj (ConstantWeightRealization.unitWeight K) ≅
    colimit (ConstantWeightHom.degree K A (SimplexCategory.mk 0)) :=
  ConstantWeightRealization.unitIso K A
end Ordinary

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C :=
  SerrePositivity.Smith.locallyPresentable_hasColimits (C := C)

-- The original Hom, object and presentability universes stay independent.
example (A : K ⥤ SimplexCategory ⥤ C) (n : SimplexCategory) :
    (SmallHomFrameWeights.functor K A).obj (ConstantWeightHom.weight K n) ≅
      colimit (ConstantWeightHom.degree K A n) := SmallHomConstantWeight.iso K A n

example : DegreeZeroHomotopyColimit.colimitFamily K I J ⟶ HomotopyColimit.functor K I J :=
  DegreeZeroHomotopyColimit.comparison K I J

example (D : K ⥤ C) : weakEquivalences C ((DegreeZeroHomotopyColimit.comparison K I J).app D) :=
  DegreeZeroHomotopyColimit.comparison_weakEquivalence K I J D

-- Augmented weights give actual maps. The weak-equivalence statement is
-- reduced to the precise remaining realization step, rather than assumed.
example (D : K ⥤ C) (W : Kᵒᵖ ⥤ SSet.{w})
    (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    (SmallHomFrameWeights.weightedFunctor K
        ((EvaluatedFrame.family K I J).obj D) W).obj (𝟙_ SSet.{w}) ⟶
      (HomotopyColimit.functor K I J).obj D := WeightedSourceComparison.comparison K I J D q

example (D : K ⥤ C) (W : Kᵒᵖ ⥤ SSet.{w})
    (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    weakEquivalences C (WeightedSourceComparison.comparison K I J D q) ↔
      weakEquivalences C ((SmallHomFrameWeights.functor K
        ((EvaluatedFrame.family K I J).obj D)).map q) :=
  WeightedSourceComparison.comparison_weakEquivalence_iff K I J D q

-- In particular the source is exactly the weighted Quillen functor used
-- by the existing weighted-holim comparison, on the canonical chosen weight.
example [ModelCategory SSet.{w}]
    (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp) (D : K ⥤ C) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    (FrameWeightedLimit.weightedFunctor K SSet.modelCategoryQuillen.I
        SSet.modelCategoryQuillen.J ((EvaluatedFrame.family K I J).obj D)).obj (𝟙_ SSet.{w}) ⟶
      (HomotopyColimit.functor K I J).obj D := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  exact WeightedSourceComparison.comparison K I J D
    (HomotopyCones.weightComparison Kᵒᵖ SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J)

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightHom,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightRealization,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomConstantWeight,
    `SerrePositivity.HomotopicalAlgebra.Diagram.DegreeZeroHomotopyColimit,
    `SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceComparison]
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
  logInfo m!"Weighted source comparison audit passed: {count} declarations in {seen.size} modules."
