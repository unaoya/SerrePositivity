import SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseMappingComparison
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DiagramModel

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

-- Frames are evaluated without assuming the input diagram is cofibrant.
example (F : K ⥤ C) (k : K) :
    reedyLeft simplex (cofibrations C)
      (initial.to ((EvaluatedFrame.frame K I J).obj (F, k))) :=
  EvaluatedFrame.reedyCofibrant K I J (F, k)

example (F : K ⥤ C) (k : K) (n : SimplexCategory) :
    weakEquivalences C (((EvaluatedFrame.augmentation K I J).app (F, k)).app n) :=
  EvaluatedFrame.augmentation_weakEquivalence K I J (F, k) n

variable (cof : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations C) (fibrations C))

-- Naturality holds simultaneously in D, k and the original target Y.
example : PointwiseMappingComparison.pointwiseRMap K cof fib ⟶
    PointwiseMappingComparison.middle K I J cof fib :=
  PointwiseMappingComparison.pointwiseLeft K I J cof fib

example : PointwiseMappingComparison.frameDiagram K I J fib ⟶
    PointwiseMappingComparison.middle K I J cof fib :=
  PointwiseMappingComparison.right K I J cof fib

-- The repackaged source is identified with the preexisting strict RMap.
example : PointwiseMappingComparison.resolvedDiagram K cof fib ≅
    PointwiseMappingComparison.pointwiseRMap K cof fib :=
  PointwiseMappingComparison.pointwiseRMapIso K cof fib

example (F : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    SSet.KanComplex ((((PointwiseMappingComparison.middle K I J cof fib).obj F).obj Y).obj k) :=
  PointwiseMappingComparison.middle_kanComplex K I J cof fib F Y k

example [ModelCategory SSet.{v}]
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (F : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{v}
        ((((PointwiseMappingComparison.pointwiseLeft K I J cof fib).app F).app Y).app k) ∧
      weakEquivalences SSet.{v}
        ((((PointwiseMappingComparison.right K I J cof fib).app F).app Y).app k) :=
  ⟨PointwiseMappingComparison.pointwiseLeft_weakEquivalence K I J cof fib hcof F Y k,
    PointwiseMappingComparison.right_weakEquivalence K I J cof fib hcof F Y k⟩

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.LatchingPreservation,
    `SerrePositivity.HomotopicalAlgebra.Diagram.EvaluatedFrame,
    `SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseMappingComparison]
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
  logInfo m!"Pointwise RMap diagram audit passed: {count} declarations in {seen.size} modules."
