import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimWeightedComparison
import Lean.Util.CollectAxioms

noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.HomotopyFunctionComplex

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]

-- Independent Hom universes, an arbitrary fixed weight, and no model on SSet.
example (W : Kᵒᵖ ⥤ SSet.{w}) :
    SmallHomFrameWeights.standardFrameHomFamily K W ⋙
        (Functor.whiskeringRight C SSet.{v} SSet.{max v w}).obj SSet.uliftFunctor.{w,v} ≅
      SmallHomFrameWeights.weightedHomFamily K W ⋙
        (Functor.whiskeringRight C SSet.{w} SSet.{max v w}).obj SSet.uliftFunctor.{v,w} :=
  SmallHomFrameWeights.standardFrameHomFamilyIso K W

variable (I J : MorphismProperty C)
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J] [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w})
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

-- The actual frame Hom cospan now connects by a bifunctor isomorphism to weighted Hom.
example : HocolimFrameComparison.frameHom K I J IS JS fib ⋙
      (Functor.whiskeringRight C SSet.{v} SSet.{max v w}).obj SSet.uliftFunctor.{w,v} ≅
    HocolimWeightedComparison.weightedHom K I J IS JS fib ⋙
      (Functor.whiskeringRight C SSet.{w} SSet.{max v w}).obj SSet.uliftFunctor.{v,w} :=
  HocolimWeightedComparison.frameHomIso K I J IS JS fib

example : HocolimWeightedComparison.weightedHom K I J IS JS fib ⟶
    HocolimWeightedComparison.holim K I J IS JS fib :=
  HocolimWeightedComparison.toHolim K I J IS JS fib

example (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
    (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((HocolimWeightedComparison.toHolim K I J IS JS fib).app D).app Y) :=
  HocolimWeightedComparison.toHolim_weakEquivalence K I J IS JS fib hcof hfib D Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomWeightAdjunctionNaturality,
    `SerrePositivity.HomotopicalAlgebra.Diagram.WeightedFrameHomNaturality,
    `SerrePositivity.HomotopicalAlgebra.Diagram.HocolimWeightedComparison]
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
  logInfo m!"Hocolim weighted comparison audit passed: {count} declarations in {seen.size} modules."
