import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimMappingComparison
import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
  (cosimplicialHom)

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w})
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (D : K ⥤ C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)

-- An actual weakly augmented resolution, not just a weakly equivalent source object.
example (n : SimplexCategory) : weakEquivalences C
    ((WeightedHomotopyColimitFrame.augmentation K I J IS JS D).app n) :=
  WeightedHomotopyColimitFrame.augmentation_weakEquivalence K I J IS JS D hcof hfib hw n

-- Both target-natural maps exist without model structures on the value universes v/max.
example : (chosenResolutionHom cof fib).obj
      (Opposite.op ((HomotopyColimit.functor K I J).obj D)) ⟶
    HocolimMappingComparison.middle K I J IS JS D cof fib :=
  HocolimMappingComparison.fromRMap K I J IS JS D cof fib

example : fibrantTarget fib ⋙ cosimplicialHom
      (WeightedHomotopyColimitFrame.frame K I J IS JS D) ⋙ SSet.uliftFunctor.{w,v} ≅
    fibrantTarget fib ⋙ FrameWeightedLimit.weightedHom K IS JS
      (WeightedSourceComparison.frames K I J D) ⋙ SSet.uliftFunctor.{v,w} :=
  HocolimMappingComparison.weightedIso K I J IS JS D fib

variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

-- All three actual nonisomorphism legs are weak equivalences in one common universe.
example (Y : C) : weakEquivalences SSet.{max v w}
    ((HocolimMappingComparison.liftedFromRMap K I J IS JS D cof fib).app Y) :=
  HocolimMappingComparison.liftedFromRMap_weakEquivalence K I J IS JS D cof fib
    hcof hfib hw hcofV hfibV hcofM hfibM Y

example (Y : C) : weakEquivalences SSet.{max v w}
    ((HocolimMappingComparison.liftedFromFrame K I J IS JS D cof fib).app Y) :=
  HocolimMappingComparison.liftedFromFrame_weakEquivalence K I J IS JS D cof fib
    hcof hfib hcofV hfibV hcofM hfibM Y

example (Y : C) : weakEquivalences SSet.{max v w}
    ((HocolimMappingComparison.liftedToHolim K I J IS JS D fib).app Y) :=
  HocolimMappingComparison.liftedToHolim_weakEquivalence K I J IS JS D fib hcof hfib hcofM hfibM Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverObject,
    `SerrePositivity.HomotopicalAlgebra.Diagram.WeightedHomotopyColimitFrame,
    `SerrePositivity.HomotopicalAlgebra.Diagram.HocolimMappingComparison]
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
  logInfo m!"Hocolim mapping comparison audit passed: {count} declarations in {seen.size} modules."
