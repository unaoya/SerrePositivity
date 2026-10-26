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
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.sphereClass_surjective
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.total_piZero_value_representative
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.total_positive_vertex_representative
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.isColimitCone_iff_liftedTotalPiCriterion
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.PiPathRelated.map
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.pathFamilyHomotopy_precomp
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_mapPiZero_bijective
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_transport_path_witness
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_transport_left_unique
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_transport_right_unique
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_transport_path_realization
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridgePiTransportEquiv
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_transport_iff_equiv
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.total_positive_pair_representative
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.shared_path_map_equality_iff
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.homotopy_map_equality_iff
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.nativeTotalComparison_leg_components
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.nativeTotalComparison_leg_equality_iff
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.isColimitCone_iff_nativeTotalPiCriterion
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.coconeLegNaturalityHomotopy
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.coconeLegNaturality_components
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_stage_positive_kernel
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.finite_positive_pair_representative
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.totalLegToKan_homotopy_valueToTotal
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.finite_nativeTotalLeg_detection
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_positive_injective
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.pathVertexEdge_exists
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.piPathRelated_iff_exists_transport
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.PiPathRelated.trans
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.PiPathRelated.symm
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.path_map_surjective_iff
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_positive_surjective
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.bridge_finite_piCriterion
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.isColimitCone_of_coherent_spacePiData
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.coconeTransportLeg_restrict
#check @SerrePositivity.InfinityCategories.F2.PiCriterion.dgBarCompactFilteredSpacePiBridge
#check @SerrePositivity.InfinityCategories.DGBarCompactFilteredSpacePiBridge

universe u v
example (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    SerrePositivity.InfinityCategories.DGBarCompactFilteredSpacePiBridge.{u, v} κ :=
  SerrePositivity.InfinityCategories.F2.PiCriterion.dgBarCompactFilteredSpacePiBridge κ

#print axioms SerrePositivity.InfinityCategories.F2.PiCriterion.dgBarCompactFilteredSpacePiBridge

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
