import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimRMapFormula
import Lean.Util.CollectAxioms

noncomputable section
universe w v u vH uH
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DiagramModel SerrePositivity.HomotopyFunctionComplex

variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w})
  [SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SerrePositivity.SimplicialHomotopy.weakEquivalences)

-- Both endpoints use the same actual original source resolutions and target replacements.
example (D : (K ⥤ C)ᵒᵖ) (Y : C) :
    ((HocolimRMapFormula.source K I J cof fib).obj D).obj Y =
      ((SmallHomComparison.chosenHom cof fib).obj
        (Opposite.op ((HomotopyColimit.functor K I J).obj D.unop))).obj Y := rfl

example (D : (K ⥤ C)ᵒᵖ) (Y : C) :
    ((HocolimRMapFormula.target K IS JS cof fib).obj D).obj Y =
      (HomotopyLimit.functor Kᵒᵖ IS JS).obj
        (((SmallPointwiseMappingComparison.pointwiseRMap K cof fib).obj D).obj Y) := rfl

-- No model on SSet(v), no common larger value model and no enrichment of C.
example (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((HocolimRMapFormula.fromSource K I J IS JS cof fib).app D).app Y) :=
  HocolimRMapFormula.fromSource_weakEquivalence K I J IS JS cof fib hcof hfib hw D Y

example (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((HocolimRMapFormula.fromBridge K I J IS JS cof fib).app D).app Y) :=
  HocolimRMapFormula.fromBridge_weakEquivalence K I J IS JS cof fib hcof hfib D Y

example (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((HocolimRMapFormula.bridgeToMiddle K I J IS JS cof fib).app D).app Y) :=
  HocolimRMapFormula.bridgeToMiddle_weakEquivalence K I J IS JS cof fib hcof hfib D Y

example (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((HocolimRMapFormula.fromTarget K I J IS JS cof fib).app D).app Y) :=
  HocolimRMapFormula.fromTarget_weakEquivalence K I J IS JS cof fib hcof hfib D Y

-- Naturality holds in both variables after any ordinary localization in independent universes.
example {H : Type uH} [Category.{vH} H] (L : SSet.{w} ⥤ H)
    [L.IsLocalization (weakEquivalences SSet.{w})] :
    (HomotopyColimit.functor K I J).op ⋙ SmallHomComparison.chosenHom cof fib ⋙
        (Functor.whiskeringRight C SSet.{w} H).obj L ≅
      PointwiseRMapHomotopyLimit.functor K IS JS cof fib ⋙
        (Functor.whiskeringRight C SSet.{w} H).obj L :=
  HocolimRMapFormula.localizedIso K I J IS JS cof fib hcof hfib hw L

-- The usual mono/Kan generation is derived, not an extra assumption at the final entrance.
example (D : (K ⥤ C)ᵒᵖ) (Y : C) :
    let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
    weakEquivalences SSet.{w} (((HocolimRMapFormula.fromSource K I J
      SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J cof fib).app D).app Y) := by
  let := SerrePositivity.SimplicialModel.simplicial_cofibrantlyGenerated hcof hfib
  exact HocolimRMapFormula.fromSource_weakEquivalence K I J
    SSet.modelCategoryQuillen.I SSet.modelCategoryQuillen.J cof fib hcof hfib hw D Y

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomFrameInvariance,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SmallPointwiseMappingComparison,
    `SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseRMapHomotopyLimit,
    `SerrePositivity.HomotopicalAlgebra.Diagram.SmallHocolimFrameComparison,
    `SerrePositivity.HomotopicalAlgebra.Diagram.HocolimRMapFormula]
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
  logInfo m!"Hocolim RMap formula audit passed: {count} declarations in {seen.size} modules."
