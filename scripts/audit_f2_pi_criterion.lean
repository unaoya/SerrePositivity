import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.All
import Lean.Util.CollectAxioms

#check @SerrePositivity.InfinityCategories.F2.PiCriterion.totalCoconeComparison
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.totalVertexComparison
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.isColimitCone_iff_totalVertexComparison_isIso
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.totalVertexComparison_eq_colimitVertexIso_hom
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.KanMapPiCriterion
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.homotopyEquivalence_iff_kanMapPiCriterion
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.isColimitCone_iff_totalPiCriterion
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.liftedBaseShapeIso
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.isColimitCone_iff_liftedBase_restrict
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.finite_mappingClass_value_representative
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.finite_constant_boundary_fiber_detection
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.pathPiEquiv
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.pathPiEquiv_map_zero
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.sphereClass_path_witness

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion |>.isPrefixOf mod do
      continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "PiCriterion: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "PiCriterion: no declarations audited"
  logInfo m!"PiCriterion audit passed: {count} declarations, standard three axioms only."
