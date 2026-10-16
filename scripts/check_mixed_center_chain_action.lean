import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u w uD vD
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra Opposite
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- All center moves use actual frame and target resolution maps.
example {q p : MixedResolutionCenters.Index C} (f : q ⟶ p) {T : SSet.{v}}
    (s : T ⟶ (MixedResolutionCenters.leftChoices C).obj q)
    (r : T ⟶ (MixedResolutionCenters.rightChoices C).obj q)
    (t : T ⟶ (MixedResolutionCenters.input C).obj (op p)) :
    MixedResolutionCenters.action C p
        (s ≫ (MixedResolutionCenters.leftChoices C).map f)
        (r ≫ (MixedResolutionCenters.rightChoices C).map f) t =
      MixedResolutionCenters.action C q s r
        (t ≫ (MixedResolutionCenters.input C).map f.op) ≫
          (MixedResolutionCenters.output C).map f :=
  MixedResolutionCenters.action_transport C f s r t

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {D : Type uD} [Category.{vD} D] (H : D ⥤ MixedResolutionCenters.Index C)
  (K : D ⥤ SSet.{v})

-- Actual whole systems exist with neither a large value model nor source functorial factorizations.
example : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.leftChoices C) :=
  NerveMixedChoices.selectedLeft C hcof H K
example : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.rightChoices C) :=
  NerveMixedChoices.selectedRight C hcof H K
example (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.leftChoices C).obj (H.obj d))
    (d : D) :
    NerveSmallFamilies.point K (H ⋙ MixedResolutionCenters.leftChoices C)
      (NerveMixedChoices.leftSystem.{v, u, w} C hcof H K families) d = families d :=
  NerveMixedChoices.left_point C hcof H K families d
example (n : ℕ) (old : NerveMovingParameter.LowerSystem (NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.rightChoices C) n) :
    Functor.whiskerLeft (SerrePositivity.Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
      (NerveMixedChoices.extendRight C hcof H K n old) = old :=
  NerveMixedChoices.extendRight_restrict C hcof H K n old

section PreserveBothWholeSystems
variable (a : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.leftChoices C))
  (b : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.rightChoices C))
example {n m : ℕ} (c : ComposableArrows D n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (t : NerveMixedAction.parameter K c ⟶ NerveMixedAction.input C H c)
    (t' : NerveMixedAction.parameter K (NerveMixedAction.reindexChain c θ) ⟶
      NerveMixedAction.input C H (NerveMixedAction.reindexChain c θ))
    (ht : (NerveMixedAction.operatorParameter K c θ ≫ t) ≫
      (MixedResolutionCenters.input C).map (NerveMixedAction.tailMap C H c θ).op =
        NerveMixedAction.prefixParameter K c θ ≫ t') :
    NerveMixedAction.operatorParameter K c θ ≫
        NerveMixedAction.action C hcof hfib H K a b c t =
      (NerveMixedAction.prefixParameter K c θ ≫
        NerveMixedAction.action C hcof hfib H K a b (NerveMixedAction.reindexChain c θ) t') ≫
          (MixedResolutionCenters.kanOutput C hcof hfib).map
            (NerveMixedAction.tailMap C H c θ) :=
  NerveMixedAction.operator_of_input C hcof hfib H K a b c θ t t' ht
end PreserveBothWholeSystems

-- This instantiation supplies actual choices on both sides; the target is in SSet[v].
example {n : ℕ} (c : ComposableArrows D n)
    (t : NerveMixedAction.parameter K c ⟶ NerveMixedAction.input C H c) :
    NerveMixedAction.parameter K c ⟶
      (MixedResolutionCenters.kanOutput C hcof hfib).obj (NerveMixedAction.center C H c) :=
  NerveMixedAction.action C hcof hfib H K
    (NerveMixedChoices.selectedLeft.{v, u, w} C hcof H K)
    (NerveMixedChoices.selectedRight.{v, u, w} C hcof H K) c t

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedDiagonalHomTransport,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.MixedResolutionCenters,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedAction,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedChoices]
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
    throwError "Some mixed center chain action modules were not audited"
  logInfo m!"Mixed center chain action audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
