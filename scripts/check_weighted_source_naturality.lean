import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimFrameComparison
import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimMappingComparison
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.HomotopyFunctionComplex

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- A genuinely natural diagram-to-hocolim comparison with independently sized Hom sets.
example {W : Kᵒᵖ ⥤ SSet.{w}} (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    WeightedSourceComparison.weightedFamily K I J W ⋙
        (evaluation SSet.{w} C).obj (𝟙_ SSet.{w}) ⟶ HomotopyColimit.functor K I J :=
  WeightedSourceComparison.comparisonFamily K I J q

example {D E : K ⥤ C} (f : D ⟶ E) {W : Kᵒᵖ ⥤ SSet.{w}}
    (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    ((WeightedSourceComparison.weightedFamily K I J W).map f).app (𝟙_ SSet.{w}) ≫
        WeightedSourceComparison.comparison K I J E q =
      WeightedSourceComparison.comparison K I J D q ≫ (HomotopyColimit.functor K I J).map f :=
  WeightedSourceComparison.comparison_naturality K I J f q

variable [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w})
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

example : WeightedHomotopyColimitFrame.frameFamily K I J IS JS ⟶
    HomotopyColimit.functor K I J ⋙ Functor.const SimplexCategory :=
  WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS

-- The chosen RMap is the actual left endpoint of a two-variable natural cospan.
example : (HomotopyColimit.functor K I J).op ⋙ chosenResolutionHom cof fib ⟶
    HocolimFrameComparison.middle K I J IS JS cof fib :=
  HocolimFrameComparison.left K I J IS JS cof fib

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

example (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{v}
    (((HocolimFrameComparison.left K I J IS JS cof fib).app D).app Y) :=
  HocolimFrameComparison.left_weakEquivalence K I J IS JS cof fib hcof hfib hw hcofV D Y

example (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{v}
    (((HocolimFrameComparison.right K I J IS JS cof fib).app D).app Y) :=
  HocolimFrameComparison.right_weakEquivalence K I J IS JS cof fib hcof hfib hcofV D Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality,
    `SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightNaturality,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomWeightFunctoriality,
    `SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceNaturality,
    `SerrePositivity.HomotopicalAlgebra.Diagram.HocolimFrameComparison]
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
  logInfo m!"Weighted source naturality audit passed: {count} declarations in {seen.size} modules."
