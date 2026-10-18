import SerrePositivity.InfinityCategories.F1
import Lean.Util.CollectAxioms

/-!
概要：F1 の全宣言の公理依存を監査する。
方針：宣言元モジュールで抽出し、生成宣言も含め再帰的に公理を調べる。
規約：許す公理は propext・Classical.choice・Quot.sound のみ。
使われ方：Kerodon §5.1 以降の各保存単位で対象ビルド後に実行する。
-/

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless `SerrePositivity.InfinityCategories.F1 |>.isPrefixOf mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "F1: unexpected axioms in {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "F1: no declarations audited"
  logInfo m!"F1 audit passed: {count} declarations, standard three axioms only."

#check @SerrePositivity.InfinityCategories.IsCartesianEdge
#check @SerrePositivity.InfinityCategories.IsCocartesianEdge
#check @SerrePositivity.InfinityCategories.isCartesianEdge_of_rightFibration
#check @SerrePositivity.InfinityCategories.isCocartesianEdge_of_leftFibration
#check @SerrePositivity.InfinityCategories.IsCartesianEdge.comp
#check @SerrePositivity.InfinityCategories.IsCocartesianEdge.comp
#check @SerrePositivity.InfinityCategories.cartesianFibrations
#check @SerrePositivity.InfinityCategories.cocartesianFibrations
#check @SerrePositivity.InfinityCategories.CartesianFibration
#check @SerrePositivity.InfinityCategories.CocartesianFibration
#check @SerrePositivity.InfinityCategories.cartesianFibration_innerFibration
#check @SerrePositivity.InfinityCategories.cocartesianFibration_innerFibration
#check @SerrePositivity.InfinityCategories.rightFibration_cartesianFibration
#check @SerrePositivity.InfinityCategories.leftFibration_cocartesianFibration
#check @SerrePositivity.InfinityCategories.cartesianFibration_comp
#check @SerrePositivity.InfinityCategories.cocartesianFibration_comp
#check @SerrePositivity.InfinityCategories.vertexFiber_quasicategory_of_innerFibration
#check @SerrePositivity.InfinityCategories.isCartesianEdge_pullback
#check @SerrePositivity.InfinityCategories.isCocartesianEdge_pullback
#check @SerrePositivity.InfinityCategories.cartesianFibration_pullback_snd
#check @SerrePositivity.InfinityCategories.cocartesianFibration_pullback_snd
#check @SerrePositivity.InfinityCategories.rightFibration_of_cartesianFibration_of_all_edges
#check @SerrePositivity.InfinityCategories.rightFibration_iff_cartesianFibration_all_edges
#check @SerrePositivity.InfinityCategories.leftFibration_of_cocartesianFibration_of_all_edges
#check @SerrePositivity.InfinityCategories.leftFibration_iff_cocartesianFibration_all_edges
#check @SerrePositivity.InfinityCategories.CocartesianEdgeLift
#check @SerrePositivity.InfinityCategories.nonempty_cocartesianEdgeLift
#check @SerrePositivity.InfinityCategories.chooseCocartesianEdgeLift
#check @SerrePositivity.InfinityCategories.cocartesianTransportObject
#check @SerrePositivity.InfinityCategories.leftFibration_lift_boundary_prism
#check @SerrePositivity.InfinityCategories.relativeEdgeSourceTarget
#check @SerrePositivity.InfinityCategories.relativeEdgeSource
#check @SerrePositivity.InfinityCategories.relativeEdgeSource_trivialKanFibration
#check @SerrePositivity.InfinityCategories.leftFibration_lift_prism
#check @SerrePositivity.InfinityCategories.prismEdgeFamily_zero
#check @SerrePositivity.InfinityCategories.prismEdgeFamily_one
#check @SerrePositivity.InfinityCategories.leftFibration_exists_transport
#check @SerrePositivity.InfinityCategories.relativeEdgeLiftSpace
#check @SerrePositivity.InfinityCategories.relativeEdgeLiftSpace_isContractibleKan
#check @SerrePositivity.InfinityCategories.relativeEdgeLiftSpaceVertexEquiv
#check @SerrePositivity.InfinityCategories.cocartesian_prism_exists_section
#check @SerrePositivity.InfinityCategories.cocartesian_prism_exists_lift
#check @SerrePositivity.InfinityCategories.cocartesian_prism_extend_boundary
#check @SerrePositivity.InfinityCategories.IsCocartesianPathVertex
#check @SerrePositivity.InfinityCategories.cocartesianPath
#check @SerrePositivity.InfinityCategories.cocartesianPathι
#check @SerrePositivity.InfinityCategories.cocartesianPathSource
#check @SerrePositivity.InfinityCategories.cocartesianPathVertex
#check @SerrePositivity.InfinityCategories.cocartesianPathSource_lift_vertex
#check @SerrePositivity.InfinityCategories.cocartesianPathSource_trivialKanFibration
#check @SerrePositivity.InfinityCategories.cocartesianFibration_lift_prism
#check @SerrePositivity.InfinityCategories.cocartesianFibration_exists_transport
#check @SerrePositivity.InfinityCategories.cocartesianLiftSpace
#check @SerrePositivity.InfinityCategories.cocartesianLiftSpace_isContractibleKan
#check @SerrePositivity.InfinityCategories.cocartesianLiftSpaceVertexEquiv
#check @SerrePositivity.InfinityCategories.ihom_map_const
#check @SerrePositivity.InfinityCategories.uncurry_const_functorVertex
#check @SerrePositivity.InfinityCategories.vertexFiberι_mono
#check @SerrePositivity.InfinityCategories.ihomVertexFiberMap
#check @SerrePositivity.InfinityCategories.ihomVertexFiberInverse
#check @SerrePositivity.InfinityCategories.ihomVertexFiberInverse_comp
#check @SerrePositivity.InfinityCategories.ihomVertexFiberIso
#check @SerrePositivity.InfinityCategories.cocartesianPathEndpoint
#check @SerrePositivity.InfinityCategories.cocartesianPathEndpoint_comp
#check @SerrePositivity.InfinityCategories.cocartesianLiftSpaceEndpoint
#check @SerrePositivity.InfinityCategories.IsContractibleKan.vertexIso
#check @SerrePositivity.InfinityCategories.cocartesianLiftSpaceEndpointIso
#check @SerrePositivity.InfinityCategories.transportSourceDiagram
#check @SerrePositivity.InfinityCategories.transportSourceDiagram_endpoint
#check @SerrePositivity.InfinityCategories.transportChoiceSpace
#check @SerrePositivity.InfinityCategories.transportChoiceSpace_isContractibleKan
#check @SerrePositivity.InfinityCategories.transportChoiceLift
#check @SerrePositivity.InfinityCategories.transportChoiceEndpoint
#check @SerrePositivity.InfinityCategories.transportChoiceEndpoint_comp
#check @SerrePositivity.InfinityCategories.transportAtChoice
#check @SerrePositivity.InfinityCategories.transportChoiceLift_vertex
#check @SerrePositivity.InfinityCategories.transportAtChoice_vertex
#check @SerrePositivity.InfinityCategories.transportAtChoice_witness
#check @SerrePositivity.InfinityCategories.transportAtChoiceIso
#check @SerrePositivity.InfinityCategories.IsCocartesianTransport
#check @SerrePositivity.InfinityCategories.transportChoiceOfPrism
#check @SerrePositivity.InfinityCategories.transportChoiceOfPrism_lift
#check @SerrePositivity.InfinityCategories.transportAtChoice_ofPrism
#check @SerrePositivity.InfinityCategories.IsCocartesianTransport.functorIso
#check @SerrePositivity.InfinityCategories.cocartesianTransport
#check @SerrePositivity.InfinityCategories.cocartesianTransport_isTransport
#check @SerrePositivity.InfinityCategories.cocartesianTransportHo
#check @SerrePositivity.InfinityCategories.IsCocartesianTransport.toHoIso
