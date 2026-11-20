import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightedLimit
import SerrePositivity.HomotopicalAlgebra.Diagram.EvaluatedFrame
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DiagramModel

section Ordinary
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  [HasColimitsOfSize.{w, w} C]

-- No model or enrichment is needed to realize an arbitrary weight diagram.
example (A : K ⥤ SimplexCategory ⥤ C) :
    FrameWeightRealization.functor K A ⊣ FrameWeightRealization.hom K A :=
  FrameWeightRealization.adjunction K A
end Ordinary

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (IC JC : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IC JC]
  [ModelCategory SSet.{w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)

-- Independent v,w,u, original model C, actual projective resolution frames.
-- The source diagram is arbitrary and no pointwise frame data is extra input.
example (D : K ⥤ C) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    SerrePositivity.Quillen.IsLeftQuillen
      (FrameWeightedLimit.weightedFunctor K SSet.modelCategoryQuillen.I
        SSet.modelCategoryQuillen.J ((EvaluatedFrame.family K IC JC).obj D)) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  exact FrameWeightedLimit.weighted_isLeftQuillen K _ _ hcof hfib _
    (fun k => EvaluatedFrame.reedyCofibrant K IC JC (D, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K IC JC (D, k))

example (D : K ⥤ C) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    FrameWeightedLimit.weightedFunctor K SSet.modelCategoryQuillen.I
        SSet.modelCategoryQuillen.J ((EvaluatedFrame.family K IC JC).obj D) ⊣
      FrameWeightedLimit.weightedHom K SSet.modelCategoryQuillen.I
        SSet.modelCategoryQuillen.J ((EvaluatedFrame.family K IC JC).obj D) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  exact FrameWeightedLimit.adjunction K _ _ _

-- An actual natural map to the existing homotopy limit is weak at every
-- fibrant target. No unproved ordinary-limit/holim identification is used.
example (D : K ⥤ C) (Y : C) [IsFibrant Y] :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    weakEquivalences SSet.{w}
      ((FrameWeightedLimit.comparison K SSet.modelCategoryQuillen.I
        SSet.modelCategoryQuillen.J ((EvaluatedFrame.family K IC JC).obj D)).app Y) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  exact FrameWeightedLimit.comparison_weakEquivalence K
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J hcof hfib
    ((EvaluatedFrame.family K IC JC).obj D)
    (fun k => EvaluatedFrame.reedyCofibrant K IC JC (D, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K IC JC (D, k)) Y

example (D : K ⥤ C)
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (Y : C) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    weakEquivalences SSet.{w}
      ((Functor.whiskerLeft (fibrantTarget fib)
        (FrameWeightedLimit.comparison K SSet.modelCategoryQuillen.I
          SSet.modelCategoryQuillen.J ((EvaluatedFrame.family K IC JC).obj D))).app Y) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  exact FrameWeightedLimit.replacedComparison_weakEquivalence K
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J hcof hfib
    ((EvaluatedFrame.family K IC JC).obj D)
    (fun k => EvaluatedFrame.reedyCofibrant K IC JC (D, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K IC JC (D, k)) fib Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightRealization,
    `SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightQuillen,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomFrameWeights,
    `SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightedLimit,
    `SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyCones]
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
  logInfo m!"Weighted frame homotopy limit audit passed: {count} declarations in {seen.size} modules."
