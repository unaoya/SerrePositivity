import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe u v uD vD w uH vH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- Reconstruction retains all original arrows and original first labels.
example {D : Type uD} [Category.{vD} D] (F : D ⥤ Type w) {n : ℕ}
    (c : ComposableArrows F.Elements n) :
    SerrePositivity.LabelledChain.lift F (c ⋙ Functor.Elements.π F) (c.obj 0).val = c :=
  SerrePositivity.LabelledChain.reconstruct F c

-- Object and Hom universes of the original category remain independent.
example (D : Type uD) [Category.{vD} D] :
    SerrePositivity.NerveHomotopyUniverse.map
      (SerrePositivity.NerveSimplexFirstFunctor.first D) =
    SSet.uliftFunctor.{max uD vD, max uD vD}.map
      (SimplexNerveAugmentation.augmentation (nerve D)) :=
  SerrePositivity.NerveSimplexFirstFunctor.augmentation_eq D

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

-- This is equality of the entire original endpoint, including all labels and maps.
example : OrdinaryBarNerveBridge.firstComposite R =
    OrdinaryBarNerveBridge.simplexAugmentation R :=
  OrdinaryBarFirstEndpoint.firstComposite_eq R

example : OrdinaryBarNerveBridge.evaluatedComposite R a b =
    OrdinaryBarEvaluatedEndpoint.evaluationNerveMap R a b ≫
      OrdinaryBarEvaluatedEndpoint.rowNerveMap R :=
  OrdinaryBarEvaluatedEndpoint.evaluatedComposite_eq R a b

example : OrdinaryBarNerveBridge.simplexAugmentation R ≫
    OrdinaryBarEvaluation.evaluation R a b =
      OrdinaryBarEvaluatedEndpoint.evaluationNerveMap R a b ≫
        OrdinaryBarEvaluatedEndpoint.smallAugmentation R :=
  OrdinaryBarEvaluatedEndpoint.augmentation_square R a b

-- The homotopy now starts at the standard augmentation, with the actual small factorization.
example : SSet.Homotopy (OrdinaryBarNerveBridge.simplexAugmentation R)
    (OrdinaryBarEvaluatedEndpoint.evaluationNerveMap R a b ≫
      OrdinaryBarEvaluatedEndpoint.rowNerveMap R) :=
  OrdinaryBarEvaluatedEndpoint.homotopy R a b

example {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map (OrdinaryBarNerveBridge.simplexAugmentation R) =
      L.map (OrdinaryBarEvaluatedEndpoint.evaluationNerveMap R a b) ≫
        L.map (OrdinaryBarEvaluatedEndpoint.rowNerveMap R) :=
  OrdinaryBarEvaluatedEndpoint.image_eq R a b L hL

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.ElementsChainLifting,
    `SerrePositivity.CategoryTheory.SimplexChainVertices,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation,
    `SerrePositivity.CategoryTheory.NerveSimplexFirstFunctor,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFirstEndpoint,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarEvaluatedEndpoint]
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
  unless modules.size == expected.size do throwError "Missing endpoint comparison modules"
  logInfo m!"Ordinary bar endpoints audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
