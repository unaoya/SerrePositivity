import SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedFreeNativeFunctor
import SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedSourceNativeAction
import SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedSourceNativeFunctor
import SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedSourceShiftAction
import Lean.Util.CollectAxioms

-- C2: explicit local validation only; this file is not added to the formal audit manifest.
#check @SerrePositivity.InfinityCategories.dgKappaPresentedFreeNativeFunctor
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedFreeNativeFunctor
#check @SerrePositivity.InfinityCategories.dgKappaPresentedFreeNativeFunctor_vertex
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedFreeNativeFunctor_vertex
#check @SerrePositivity.InfinityCategories.dgKappaPresentedFreeNativeCoreFunctor
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedFreeNativeCoreFunctor
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeAction
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeAction
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeAction_id
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeAction_id
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeAction_comp
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeAction_comp
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeFunctor
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeFunctor
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeFunctor_vertex
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeFunctor_vertex
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeCoreFunctor
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeCoreFunctor
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceShiftFunctor
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceShiftFunctor
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceShiftFunctor_obj
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceShiftFunctor_obj
#check @SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeShift
#print axioms SerrePositivity.InfinityCategories.dgKappaPresentedSourceNativeShift

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let expected : Array Name := #[
    `SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedFreeNativeFunctor,
    `SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedSourceNativeAction,
    `SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedSourceNativeFunctor,
    `SerrePositivity.Archive.InfinityCategories.DGKappaDiagnostics.DGKappaPresentedSourceShiftAction
  ]
  let mut seen : Array Name := #[]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.modules[idx.toNat]!.module
    unless expected.contains owner do continue
    if let .axiomInfo _ := info then throwError "C2: axiom declaration: {name}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "C2: unexpected axioms in {name}: {axioms}"
    unless seen.contains owner do seen := seen.push owner
    count := count + 1
  for owner in expected do
    unless seen.contains owner do throwError "C2: destination module not audited: {owner}"
  logInfo m!"C2: {count} declarations in {seen.size} destination modules; only standard axioms."
