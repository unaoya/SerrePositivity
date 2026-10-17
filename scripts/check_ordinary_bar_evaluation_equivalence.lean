import SerrePositivity.HomotopicalAlgebra.Rectification.Foundations
import Lean.Util.CollectAxioms

universe v u uD vD
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex

-- The new general preservation theorem has no value model assumption.
example {X Y : SSet.{max u v}} (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (SimplexNerve.functor.map f)) :=
  SimplexNerve.map_localized_isIso f hf

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

-- Actual labelled natural transformation and interval retain the original raw augmentation.
example : OrdinaryBarReferenceRows.referenceElements R ⟶ OrdinaryBarReferenceRows.rowElements R :=
  OrdinaryBarReferenceRows.comparison R

example : SSet.Homotopy (OrdinaryBarReferenceRowHomotopy.fromReference R)
    (OrdinaryBarReferenceRowHomotopy.fromRows R) := OrdinaryBarReferenceRowHomotopy.homotopy R

example : OrdinaryBarReferenceRowHomotopy.fromReference R =
    OrdinaryBarReferenceRowHomotopy.referenceComposite R :=
  OrdinaryBarReferenceRowHomotopy.reference_factorization R

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R)) [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- Arbitrary coherent systems; no ModelCategory SSet.{max u v} or functorial source data.
include hcof hfib in
example : IsIso (AnodyneHomotopy.anodyneQ.map (OrdinaryBarEvaluation.evaluation R a b)) :=
  OrdinaryBarEvaluationEquivalence.evaluation_isIso R a b hcof hfib

include hcof hfib in
example {D : Type uD} [Category.{vD} D] (L : SSet.{max u v} ⥤ D)
    (hL : SSet.anodyneExtensions.IsInvertedBy L) :
    IsIso (L.map (OrdinaryBarEvaluation.evaluation R a b)) :=
  OrdinaryBarEvaluationEquivalence.evaluation_image_isIso R a b hcof hfib L hL

include hcof hfib in
example : IsIso (Functor.whiskerRight (OrdinaryResolutionBar.right (C := C))
    AnodyneHomotopy.anodyneQ) :=
  OrdinaryBarEvaluationEquivalence.right_natural_isIso hcof hfib

include hcof hfib in
example : IsIso (Functor.whiskerRight (OrdinaryResolutionBar.ordinaryRight (C := C))
    AnodyneHomotopy.anodyneQ) :=
  OrdinaryBarEvaluationEquivalence.ordinaryRight_natural_isIso hcof hfib

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveEquivalence,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReferenceRows,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarReferenceRowHomotopy,
    `SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarEvaluationEquivalence]
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
  unless modules.size == expected.size do
    throwError "Missing ordinary bar evaluation equivalence modules"
  logInfo m!"Ordinary bar evaluation equivalence audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
