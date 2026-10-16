import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u uD vD uB vB uH vH
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- Actual maps, natural in every simplicial operator, without a simplicial model.
example (X : SSet.{v}) : nerve X.Elements ⟶ X :=
  SimplexNerveAugmentation.augmentation X

example {X Y : SSet.{v}} (f : X ⟶ Y) :
    nerveMap f.mapElements ≫ SimplexNerveAugmentation.augmentation Y =
      SimplexNerveAugmentation.augmentation X ≫ f :=
  SimplexNerveAugmentation.naturality X f

-- Independent index, base, and value universes in the generic total-to-bar map.
example {D : Type uD} [Category.{vD} D] (F : D ⥤ SSet.{v}) :
    nerve (BarConstruction.TotalNerve.Total F) ⟶ (BarConstruction.functor D).obj F :=
  BarConstruction.TotalNerve.augmentation F

example {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
    (p : D ⥤ B) (F : D ⥤ SSet.{v}) (b : B) :
    BarConstruction.commaBar p F b ≅ (BarConstruction.relative p F).obj b :=
  BarConstruction.commaPresentation p F b

example {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]
    (p : D ⥤ B) (F : D ⥤ SSet.{v}) (b : B) :
    nerve (BarConstruction.TotalNerve.Total (BarConstruction.commaValues p F b)) ⟶
      (BarConstruction.relative p F).obj b :=
  BarConstruction.totalNerveAugmentation p F b

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)
  (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

-- This target is the actual original ordinary bar, retaining the same total index.
example : nerve (OrdinaryBarTotalCone.Total R) ⟶ OrdinaryBarEvaluation.bar R :=
  OrdinaryBarNerveBridge.rawBridge R

example : SSet.Homotopy (OrdinaryBarNerveBridge.firstComposite R)
    (OrdinaryBarNerveBridge.evaluatedComposite R a b) :=
  OrdinaryBarNerveBridge.homotopy R a b

example {H : Type uH} [Category.{vH} H] (L : SSet.{max u v} ⥤ H)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    L.map (OrdinaryBarNerveBridge.firstComposite R) =
      L.map (OrdinaryBarNerveBridge.evaluatedComposite R a b) :=
  OrdinaryBarNerveBridge.image_eq R a b L hL

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.CategoryTheory.SimplexChainParameter,
    `SerrePositivity.CategoryTheory.LabelledChain,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveAugmentation,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.TotalNerveBarAugmentation,
    `SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarCommaPresentation,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarNerveBridge]
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
  unless modules.size == expected.size do throwError "Missing nerve bridge modules"
  logInfo m!"Ordinary bar nerve bridge audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
