import SerrePositivity.EInfinity
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Ring

-- 必須宣言はコード生成の再帰上限を避けるため、noinline の小配列に分ける。
-- 追加時も各配列を128項目以内とし、下の配列一覧へ必ず含める。
@[noinline] private def e2RequiredBatch0 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Segment.map_eqToHom_of_eq,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_source_target_of_eq,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux_eqToHom_of_eq,
      `SerrePositivity.EInfinity.Hammock.WordAction.column_eqToHom_of_cut_eq,
      `SerrePositivity.EInfinity.Hammock.WordAction.source_target_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.app_cut_eq_adjacent,
      `SerrePositivity.EInfinity.Hammock.WordAction.app_cut_eq_of_le,
      `SerrePositivity.EInfinity.Hammock.WordAction.app_cut_eq,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingVertex,
      `SerrePositivity.EInfinity.Hammock.WordAction.cut_embeddingVertex,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingApp,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingApp_mem,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingApp_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.eqToHom_heq_of_endpoints,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingApp_first,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingApp_last,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingApp_comm,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingPreimage,
      `SerrePositivity.EInfinity.Hammock.WordAction.map_embeddingPreimage,
      `SerrePositivity.EInfinity.Hammock.WordAction.embeddingPreimage_map,
      `SerrePositivity.EInfinity.Hammock.WordAction.functor_full,
      `SerrePositivity.EInfinity.Hammock.nerveChainLift,
      `SerrePositivity.EInfinity.Hammock.nerveChainLift_comp,
      `SerrePositivity.EInfinity.Hammock.nerveMap_range_iff,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_map_range_iff,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_full,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransitionPreimage,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_map_preimage,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_preimage_map,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphMap_range_iff,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_image_castSucc,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_image_succ,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_surjective,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_image_source,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_image_target,
      `SerrePositivity.EInfinity.Hammock.Zigzag.arrow_heq_of_eq,
      `SerrePositivity.EInfinity.Hammock.WordAction.vertex_image_castSucc,
      `SerrePositivity.EInfinity.Hammock.WordAction.vertex_image_succ,
      `SerrePositivity.EInfinity.Hammock.WordAction.arrow_image_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.obj_injective,
      `SerrePositivity.EInfinity.Hammock.WordAction.functor_faithful,
      `SerrePositivity.EInfinity.Hammock.nerveMap_mono_of_faithful,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_map_mono,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_map_app_injective,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_empty_fiber,
      `SerrePositivity.EInfinity.Hammock.WordAction.empty_fiber_arrow_heq,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_obj_injective,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_faithful,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphMap_mono,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphMap_app_injective,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_image_arrow_heq,
      `SerrePositivity.EInfinity.Hammock.Word.append_assoc,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.vertex_assoc,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.arrow_assoc_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.obj_assoc_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_assoc_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.map_assoc_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.functor_assoc,
      `SerrePositivity.EInfinity.Hammock.graphComposition_assoc,
      `SerrePositivity.EInfinity.Hammock.tensorTriple_hom_ext,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_assoc_left_fac,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_assoc_right_fac,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_assoc,
      `SerrePositivity.EInfinity.Hammock.enrichedCategory,
      `SerrePositivity.EInfinity.Hammock.enrichedCategory_hom,
      `SerrePositivity.EInfinity.Hammock.enrichedCategory_id,
      `SerrePositivity.EInfinity.Hammock.enrichedCategory_comp,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitComposition_assoc,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEnrichedCategory,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEnrichedCategory_hom,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEnrichedCategory_id,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEnrichedCategory_comp,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTensorTriple_hom_ext,
      `SerrePositivity.EInfinity.Hammock.Word.object_ext,
      `SerrePositivity.EInfinity.Hammock.Word.empty_append,
      `SerrePositivity.EInfinity.Hammock.Word.append_empty,
      `SerrePositivity.EInfinity.Hammock.Zigzag.object_word_hext,
      `SerrePositivity.EInfinity.Hammock.Zigzag.hom_word_hext,
      `SerrePositivity.EInfinity.Hammock.WordAction.obj_eqToHom_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.map_eqToHom_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.empty_left_obj_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.empty_right_obj_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.empty_left_map_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.empty_right_map_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.empty_left_functor,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.empty_right_functor,
      `SerrePositivity.EInfinity.Hammock.graphComposition_left_unit,
      `SerrePositivity.EInfinity.Hammock.graphComposition_right_unit,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_left_unit_fac,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_right_unit_fac,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_left_unit,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_right_unit,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitComposition_left_unit,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitComposition_right_unit,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitComposition_left_unit_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitComposition_right_unit_fac,
      `SerrePositivity.EInfinity.Hammock.tensorPairCocone,
      `SerrePositivity.EInfinity.Hammock.tensorPairCocone_isColimit,
      `SerrePositivity.EInfinity.Hammock.tensorPairCocone_ι,
      `SerrePositivity.EInfinity.Hammock.tensorPairColimitIso,
      `SerrePositivity.EInfinity.Hammock.tensorPairColimitIso_fac,
      `SerrePositivity.EInfinity.Hammock.colimitComposition,
      `SerrePositivity.EInfinity.Hammock.colimitComposition_fac,
      `SerrePositivity.EInfinity.Hammock.tensorPairColimitIso_comp,
      `SerrePositivity.EInfinity.Hammock.tensorPair_hom_ext,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTensorPairColimitIso,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitComposition,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitComposition_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTensorPairColimitIso_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTensorPairColimitIso_comp,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTensorPair_hom_ext,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphComposition_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockPairDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockCompositionCocone,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitCompositionPairing,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitCompositionPairing_fac,
      `SerrePositivity.EInfinity.Hammock.pairDiagram,
      `SerrePositivity.EInfinity.Hammock.graphPairing,
      `SerrePositivity.EInfinity.Hammock.graphPairing_naturality,
      `SerrePositivity.EInfinity.Hammock.compositionPairingCocone,
      `SerrePositivity.EInfinity.Hammock.colimitCompositionPairing,
      `SerrePositivity.EInfinity.Hammock.colimitCompositionPairing_fac,
      `SerrePositivity.EInfinity.Hammock.Direction.op_heq,
      `SerrePositivity.EInfinity.Hammock.Direction.forward_arrow_heq,
      `SerrePositivity.EInfinity.Hammock.Direction.backward_arrow_heq,
      `SerrePositivity.EInfinity.Hammock.Direction.arrow_heq_of,
      `SerrePositivity.EInfinity.Hammock.Direction.raw_heq_of_op_heq,
      `SerrePositivity.EInfinity.Hammock.Direction.raw_arrow_heq_of]

@[noinline] private def e2RequiredBatch1 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.graphComposition_naturality,
      `SerrePositivity.EInfinity.Hammock.Segment.blockPosition,
      `SerrePositivity.EInfinity.Hammock.Segment.block_index,
      `SerrePositivity.EInfinity.Hammock.Segment.chain_block,
      `SerrePositivity.EInfinity.Hammock.Segment.map_block_heq,
      `SerrePositivity.EInfinity.Hammock.Word.leftBlock,
      `SerrePositivity.EInfinity.Hammock.Word.rightBlock,
      `SerrePositivity.EInfinity.Hammock.Word.leftBlock_vertex,
      `SerrePositivity.EInfinity.Hammock.Word.leftBlock_column,
      `SerrePositivity.EInfinity.Hammock.Word.rightBlock_vertex,
      `SerrePositivity.EInfinity.Hammock.Word.rightBlock_column,
      `SerrePositivity.EInfinity.Hammock.Word.leftVertex_mono,
      `SerrePositivity.EInfinity.Hammock.Word.rightVertex_mono,
      `SerrePositivity.EInfinity.Hammock.Word.append_left_direction,
      `SerrePositivity.EInfinity.Hammock.Word.append_right_direction,
      `SerrePositivity.EInfinity.Hammock.Word.rightVertex_sub,
      `SerrePositivity.EInfinity.Hammock.Word.Block,
      `SerrePositivity.EInfinity.Hammock.Word.Block.column,
      `SerrePositivity.EInfinity.Hammock.Word.Block.vertex,
      `SerrePositivity.EInfinity.Hammock.Word.Block.vertex_monotone,
      `SerrePositivity.EInfinity.Hammock.Word.Block.vertex_sub,
      `SerrePositivity.EInfinity.Hammock.Word.Block.source_eq,
      `SerrePositivity.EInfinity.Hammock.Word.Block.target_eq,
      `SerrePositivity.EInfinity.Hammock.Word.Block.interval_direction,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.direction_left_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.direction_right_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_naturality,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.functor_naturality,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.direction_naturality_left,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.direction_naturality_right,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.arrow_naturality,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.obj_naturality,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.vertex_naturality,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.arrow_index_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.map_left_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.map_right_heq,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphComposition,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphComposition_vertex,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphComposition_map,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphUnit,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitUnit,
      `SerrePositivity.EInfinity.Hammock.graphComposition,
      `SerrePositivity.EInfinity.Hammock.graphComposition_app,
      `SerrePositivity.EInfinity.Hammock.graphComposition_vertex,
      `SerrePositivity.EInfinity.Hammock.graphComposition_map,
      `SerrePositivity.EInfinity.Hammock.NerveProduct.pair,
      `SerrePositivity.EInfinity.Hammock.NerveProduct.unpair,
      `SerrePositivity.EInfinity.Hammock.NerveProduct.iso,
      `SerrePositivity.EInfinity.Hammock.NerveProduct.pair_natural,
      `SerrePositivity.EInfinity.Hammock.emptyObj,
      `SerrePositivity.EInfinity.Hammock.graphUnit,
      `SerrePositivity.EInfinity.Hammock.colimitUnit,
      `SerrePositivity.EInfinity.Hammock.graphUnit_vertex,
      `SerrePositivity.EInfinity.Hammock.Word.append,
      `SerrePositivity.EInfinity.Hammock.Word.append_direction_left,
      `SerrePositivity.EInfinity.Hammock.Word.append_direction_right,
      `SerrePositivity.EInfinity.Hammock.Word.appendMap,
      `SerrePositivity.EInfinity.Hammock.Word.appendMap_left,
      `SerrePositivity.EInfinity.Hammock.Word.appendMap_right,
      `SerrePositivity.EInfinity.Hammock.Word.appendMap_id,
      `SerrePositivity.EInfinity.Hammock.Word.appendMap_comp,
      `SerrePositivity.EInfinity.Hammock.Word.appendFunctor,
      `SerrePositivity.EInfinity.Hammock.Word.cut_append_left,
      `SerrePositivity.EInfinity.Hammock.Word.cut_append_right,
      `SerrePositivity.EInfinity.Hammock.Word.leftVertex,
      `SerrePositivity.EInfinity.Hammock.Word.rightVertex,
      `SerrePositivity.EInfinity.Hammock.Word.leftVertex_zero,
      `SerrePositivity.EInfinity.Hammock.Word.rightVertex_last,
      `SerrePositivity.EInfinity.Hammock.Word.jointVertex,
      `SerrePositivity.EInfinity.Hammock.Word.source_left,
      `SerrePositivity.EInfinity.Hammock.Word.target_left,
      `SerrePositivity.EInfinity.Hammock.Word.source_right,
      `SerrePositivity.EInfinity.Hammock.Word.target_right,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_id,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_comp,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.functor,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.left_comm,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.right_comm,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.map,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.source_left_eq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.target_left_eq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.source_right_eq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.target_right_eq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.leftArrow,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.rightArrow,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.leftArrow_mem,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.rightArrow_mem,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.obj,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.arrow_left_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.arrow_right_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_mem,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_index_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_left_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.joint_app_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.app_right_heq,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.leftIndex,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.rightIndex,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.vertex,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.vertex_le,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.vertex_gt,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.vertex_left,
      `SerrePositivity.EInfinity.Hammock.ZigzagAppend.vertex_right,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphDiagram_obj,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphDiagram_map,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitGraph,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphInclusion_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphCocone,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphCocone_isColimit,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockColimitNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockColimitComparison,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockColimitComparison_fac,
      `SerrePositivity.EInfinity.Hammock.colimitGraph,
      `SerrePositivity.EInfinity.Hammock.graphInclusion,
      `SerrePositivity.EInfinity.Hammock.graphInclusion_naturality,
      `SerrePositivity.EInfinity.Hammock.colimitGraph_isColimit,
      `SerrePositivity.EInfinity.Hammock.colimitGraphDesc,
      `SerrePositivity.EInfinity.Hammock.graphInclusion_desc,
      `SerrePositivity.EInfinity.Hammock.colimitGraph_hom_ext,
      `SerrePositivity.EInfinity.Hammock.categoryDiagram,
      `SerrePositivity.EInfinity.Hammock.graphDiagram,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_obj,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_map,
      `SerrePositivity.EInfinity.Hammock.Segment.adjacent_direction,
      `SerrePositivity.EInfinity.Hammock.Segment.map_adjacent,
      `SerrePositivity.EInfinity.Hammock.Segment.fin_map_heq]

@[noinline] private def e2RequiredBatch2 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Segment.map_parent_heq,
      `SerrePositivity.EInfinity.Hammock.Segment.chain_obj_coordinate,
      `SerrePositivity.EInfinity.Hammock.Segment.inclusion,
      `SerrePositivity.EInfinity.Hammock.Segment.index_inclusion,
      `SerrePositivity.EInfinity.Hammock.Segment.arrow_heq,
      `SerrePositivity.EInfinity.Hammock.Segment.chain_restriction,
      `SerrePositivity.EInfinity.Hammock.Segment.coordinate,
      `SerrePositivity.EInfinity.Hammock.Segment.index_coordinate,
      `SerrePositivity.EInfinity.Hammock.Segment.coordinate_monotone,
      `SerrePositivity.EInfinity.Hammock.Segment.map_comp,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux_forward_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux_backward_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.segment_direction_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.arrow_obj_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.column_comp_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.obj_comp,
      `SerrePositivity.EInfinity.Hammock.WordAction.functor_comp,
      `SerrePositivity.EInfinity.Hammock.WordAction.segment_heq_of_eq,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux_arrow_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.column_id_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.obj_id,
      `SerrePositivity.EInfinity.Hammock.WordAction.functor_id,
      `SerrePositivity.EInfinity.Hammock.WordAction.interval_direction,
      `SerrePositivity.EInfinity.Hammock.WordAction.interval_index_ge,
      `SerrePositivity.EInfinity.Hammock.WordAction.interval_index_le,
      `SerrePositivity.EInfinity.Hammock.WordAction.intervalPosition,
      `SerrePositivity.EInfinity.Hammock.WordAction.index_intervalPosition,
      `SerrePositivity.EInfinity.Hammock.WordAction.intervalPosition_zero,
      `SerrePositivity.EInfinity.Hammock.WordAction.intervalPosition_last,
      `SerrePositivity.EInfinity.Hammock.WordAction.chain_obj,
      `SerrePositivity.EInfinity.Hammock.WordAction.map_chain_heq,
      `SerrePositivity.EInfinity.Hammock.WordAction.segment_obj,
      `SerrePositivity.EInfinity.Hammock.Zigzag.object_ext,
      `SerrePositivity.EInfinity.Hammock.Zigzag.hom_hext,
      `SerrePositivity.EInfinity.Hammock.Zigzag.app_heq,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockZigzag,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphMap,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_vertex,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_app,
      `SerrePositivity.EInfinity.Hammock.Direction.category,
      `SerrePositivity.EInfinity.Hammock.Direction.vertex,
      `SerrePositivity.EInfinity.Hammock.Direction.allowed,
      `SerrePositivity.EInfinity.Hammock.Direction.arrow,
      `SerrePositivity.EInfinity.Hammock.Direction.transport_mem,
      `SerrePositivity.EInfinity.Hammock.Direction.arrow_allowed,
      `SerrePositivity.EInfinity.Hammock.Segment.index,
      `SerrePositivity.EInfinity.Hammock.Segment.index_zero,
      `SerrePositivity.EInfinity.Hammock.Segment.index_last,
      `SerrePositivity.EInfinity.Hammock.Segment.chain,
      `SerrePositivity.EInfinity.Hammock.Segment.map,
      `SerrePositivity.EInfinity.Hammock.Segment.eqToHom_mem,
      `SerrePositivity.EInfinity.Hammock.Segment.chain_map_mem,
      `SerrePositivity.EInfinity.Hammock.Segment.map_allowed,
      `SerrePositivity.EInfinity.Hammock.Segment.point_transport,
      `SerrePositivity.EInfinity.Hammock.Segment.forward_map_comm,
      `SerrePositivity.EInfinity.Hammock.Segment.backward_map_comm,
      `SerrePositivity.EInfinity.Hammock.Segment.square_transport,
      `SerrePositivity.EInfinity.Hammock.Segment.forward_arrow_comm,
      `SerrePositivity.EInfinity.Hammock.Segment.backward_arrow_comm,
      `SerrePositivity.EInfinity.Hammock.Segment.forwardChainHom,
      `SerrePositivity.EInfinity.Hammock.Segment.backwardChainHom,
      `SerrePositivity.EInfinity.Hammock.Segment.map_refl,
      `SerrePositivity.EInfinity.Hammock.WordAction.source,
      `SerrePositivity.EInfinity.Hammock.WordAction.target,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux,
      `SerrePositivity.EInfinity.Hammock.WordAction.column,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux_mem,
      `SerrePositivity.EInfinity.Hammock.WordAction.column_mem,
      `SerrePositivity.EInfinity.Hammock.WordAction.obj,
      `SerrePositivity.EInfinity.Hammock.WordAction.square,
      `SerrePositivity.EInfinity.Hammock.WordAction.segment_square,
      `SerrePositivity.EInfinity.Hammock.WordAction.columnAux_comm,
      `SerrePositivity.EInfinity.Hammock.WordAction.column_comm,
      `SerrePositivity.EInfinity.Hammock.WordAction.fixed_app,
      `SerrePositivity.EInfinity.Hammock.WordAction.map,
      `SerrePositivity.EInfinity.Hammock.WordAction.functor,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.leftColumns,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.mem_leftColumns,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cutNat,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cutNat_le_iff,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cutNat_le_length,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.lt_cut_iff,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.vertex_ext,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_zero,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_last,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_id,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_comp,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.cut_monotone,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.fiber_iff,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.fiber_direction,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.obj,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.map,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.functor,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.preimage,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.recoverObj,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.normalizationHom,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.normalizationInv,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.normalizationIso,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.equivalence,
      `SerrePositivity.EInfinity.Hammock.ThreeArrow.nerveMap_localized_isIso,
      `SerrePositivity.EInfinity.Hammock.Direction,
      `SerrePositivity.EInfinity.Hammock.Word,
      `SerrePositivity.EInfinity.Hammock.Word.Hom,
      `SerrePositivity.EInfinity.Hammock.Word.hom_ext,
      `SerrePositivity.EInfinity.Hammock.Word.id_apply,
      `SerrePositivity.EInfinity.Hammock.Word.comp_apply,
      `SerrePositivity.EInfinity.Hammock.Word.empty,
      `SerrePositivity.EInfinity.Hammock.Word.fromEmpty,
      `SerrePositivity.EInfinity.Hammock.Word.fromEmpty_unique,
      `SerrePositivity.EInfinity.Hammock.Word.emptyIsInitial,
      `SerrePositivity.EInfinity.Hammock.Word.single,
      `SerrePositivity.EInfinity.Hammock.Word.threeArrow,
      `SerrePositivity.EInfinity.Hammock.Word.source,
      `SerrePositivity.EInfinity.Hammock.Word.target,
      `SerrePositivity.EInfinity.Hammock.Zigzag,
      `SerrePositivity.EInfinity.Hammock.Zigzag.Hom,
      `SerrePositivity.EInfinity.Hammock.Zigzag.hom_ext,
      `SerrePositivity.EInfinity.Hammock.Zigzag.id_app,
      `SerrePositivity.EInfinity.Hammock.Zigzag.comp_app,
      `SerrePositivity.EInfinity.Hammock.Zigzag.evaluation,
      `SerrePositivity.EInfinity.Hammock.graph,
      `SerrePositivity.EInfinity.Hammock.Zigzag.postcomposeObj,
      `SerrePositivity.EInfinity.Hammock.Zigzag.postcomposeMap,
      `SerrePositivity.EInfinity.Hammock.Zigzag.postcompose,
      `SerrePositivity.EInfinity.Hammock.Zigzag.postcompose_id]

@[noinline] private def e2RequiredBatch3 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Zigzag.postcompose_comp,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraph,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockGraphNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockGraphNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockGraphNerveMap_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockGraphComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceHammockGraphComparisonIso_fac,
      `SerrePositivity.EInfinity.BarrattEccles.operad,
      `SerrePositivity.EInfinity.BarrattEccles.augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.augmentation_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.complexContraction,
      `SerrePositivity.EInfinity.BarrattEccles.equivariantBasis_rightAction,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonalDegree_eq_sum,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_projection,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_natural,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_coassoc,
      `SerrePositivity.EInfinity.AlexanderWhitney.counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_left_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.diagonal_right_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.counit_natural,
      `SerrePositivity.EInfinity.NegativeTensor.comparison,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_natural,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_associator,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_leftUnitor,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_rightUnitor,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_projection_generator,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_coassoc,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_left_counit,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_right_counit,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_rightAction,
      `SerrePositivity.EInfinity.BarrattEccles.cochainCounit_eq_augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_coassoc,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_left_counit,
      `SerrePositivity.EInfinity.BarrattEccles.complexDiagonal_right_counit,
      `SerrePositivity.EInfinity.Shuffle.simplex_σ_left,
      `SerrePositivity.EInfinity.Shuffle.simplex_σ_right,
      `SerrePositivity.EInfinity.Shuffle.normalizedBilinear_normalization,
      `SerrePositivity.EInfinity.Shuffle.component,
      `SerrePositivity.EInfinity.Shuffle.component_generators,
      `SerrePositivity.EInfinity.Shuffle.component_natural,
      `SerrePositivity.EInfinity.Shuffle.frontPath,
      `SerrePositivity.EInfinity.Shuffle.backPath,
      `SerrePositivity.EInfinity.Shuffle.simplex_frontCut,
      `SerrePositivity.EInfinity.Shuffle.simplex_backCut,
      `SerrePositivity.EInfinity.Shuffle.aw_component_simplex,
      `SerrePositivity.EInfinity.Shuffle.pathCutEquiv,
      `SerrePositivity.EInfinity.Shuffle.sign_eq_pow_inversionNumber,
      `SerrePositivity.EInfinity.Shuffle.inversionNumber_edgeJoin,
      `SerrePositivity.EInfinity.Shuffle.pathCut_sign,
      `SerrePositivity.EInfinity.Shuffle.signed_sum_pathCut,
      `SerrePositivity.EInfinity.Shuffle.diagonal_value_split_sum,
      `SerrePositivity.EInfinity.Shuffle.diagonal_value,
      `SerrePositivity.EInfinity.Shuffle.component_diagonal,
      `SerrePositivity.EInfinity.Shuffle.simplex_horizontal_face,
      `SerrePositivity.EInfinity.Shuffle.simplex_vertical_face,
      `SerrePositivity.EInfinity.Shuffle.sum_mixedBoundary_eq_zero,
      `SerrePositivity.EInfinity.Shuffle.shuffleBilinear_d_positive,
      `SerrePositivity.EInfinity.Shuffle.shuffleBilinear_d_leftZero,
      `SerrePositivity.EInfinity.Shuffle.shuffleBilinear_d_rightZero,
      `SerrePositivity.EInfinity.Shuffle.component_d_positive,
      `SerrePositivity.EInfinity.Shuffle.degreeMap_d,
      `SerrePositivity.EInfinity.Shuffle.chainMap,
      `SerrePositivity.EInfinity.Shuffle.ι_chainMap,
      `SerrePositivity.EInfinity.Shuffle.chainMap_natural,
      `SerrePositivity.EInfinity.Shuffle.chainMap_generators,
      `SerrePositivity.EInfinity.NatTensor.shapeSymmetry,
      `SerrePositivity.EInfinity.NatTensor.symmetry,
      `SerrePositivity.EInfinity.NatTensor.interchange,
      `SerrePositivity.EInfinity.NatTensor.inclusion_interchange,
      `SerrePositivity.EInfinity.Shuffle.chainMap_diagonal,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_symmetry,
      `SerrePositivity.EInfinity.NegativeTensor.comparison_interchange,
      `SerrePositivity.EInfinity.NegativeTensor.binaryMap_comultiplication,
      `SerrePositivity.EInfinity.Shuffle.cochainMap_diagonal,
      `SerrePositivity.EInfinity.BarrattEccles.simplicialPartialComposition,
      `SerrePositivity.EInfinity.BarrattEccles.partialComposition_eq_generalShuffle,
      `SerrePositivity.EInfinity.BarrattEccles.partialComposition_diagonal_tensorμ,
      `SerrePositivity.EInfinity.Operad.hadamard,
      `SerrePositivity.EInfinity.Operad.Hadamard.separate_swap,
      `SerrePositivity.EInfinity.Operad.Hadamard.nested_assoc,
      `SerrePositivity.EInfinity.Operad.Hadamard.parallel_assoc,
      `SerrePositivity.EInfinity.Operad.Hopf,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainDiagonal_vertex,
      `SerrePositivity.EInfinity.BarrattEccles.unit_diagonal,
      `SerrePositivity.EInfinity.BarrattEccles.hopfDiagonal,
      `SerrePositivity.EInfinity.BarrattEccles.hopf,
      `SerrePositivity.EInfinity.tensorCoInsertionAction,
      `SerrePositivity.EInfinity.tensorCoInsertionAction_coeff,
      `SerrePositivity.EInfinity.tensorCoComposition_coeff,
      `SerrePositivity.EInfinity.Operad.Coalgebra,
      `SerrePositivity.EInfinity.Operad.CoalgebraHom,
      `SerrePositivity.EInfinity.Operad.Coalgebra.forget,
      `SerrePositivity.EInfinity.Operad.restrictCoalgebra,
      `SerrePositivity.EInfinity.tensorUnitPowerIso_append,
      `SerrePositivity.EInfinity.tensorUnitPower_permutation,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.endpoint_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.restrict,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_post,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_pre,
      `SerrePositivity.EInfinity.Operad.convolutionAction,
      `SerrePositivity.EInfinity.Operad.convolutionAction_uncurry,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.prepathComplex,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constantNat,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationNat,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_one,
      `SerrePositivity.EInfinity.convolutionUnitLaw,
      `SerrePositivity.EInfinity.Operad.convolutionAction_unit,
      `SerrePositivity.EInfinity.tensorPowerSeparation,
      `SerrePositivity.EInfinity.tensorPowerSeparation_permutation,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_separation,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_permutation,
      `SerrePositivity.EInfinity.convolutionAssembly_naturality,
      `SerrePositivity.EInfinity.Operad.convolutionAction_equivariance,
      `SerrePositivity.EInfinity.Operad.convolutionAction_post,
      `SerrePositivity.EInfinity.tensorSeparation_twice,
      `SerrePositivity.EInfinity.tensorPowerSeparation_append,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_index,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_append,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_split,
      `SerrePositivity.EInfinity.tensorCoInsertionAction_zero,
      `SerrePositivity.EInfinity.tensorInsertionAction_zero_append,
      `SerrePositivity.EInfinity.convolutionAssembly_transport,
      `SerrePositivity.EInfinity.convolutionAssembly_tensorRight,
      `SerrePositivity.EInfinity.Operad.Algebra.comp_action_of_first]

@[noinline] private def e2RequiredBatch4 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Operad.Algebra.ofFirstComposition,
      `SerrePositivity.EInfinity.Operad.convolutionAction_firstBlock_evaluation,
      `SerrePositivity.EInfinity.Operad.convolutionAction_insertion_zero_evaluation,
      `SerrePositivity.EInfinity.Operad.Hopf.diagonalComponent,
      `SerrePositivity.EInfinity.convolutionAssembly_composition,
      `SerrePositivity.EInfinity.convolutionAssembly_composition_of_maps,
      `SerrePositivity.EInfinity.convolutionAssembly_pre,
      `SerrePositivity.EInfinity.Operad.convolutionUncurriedAction_comp_zero,
      `SerrePositivity.EInfinity.Operad.convolutionAction_comp_zero,
      `SerrePositivity.EInfinity.Operad.convolutionAction_comp,
      `SerrePositivity.EInfinity.Operad.convolutionAlgebra,
      `SerrePositivity.EInfinity.Operad.convolutionAction_pre,
      `SerrePositivity.EInfinity.Operad.convolutionFunctor,
      `SerrePositivity.EInfinity.Operad.convolutionPreNat,
      `SerrePositivity.EInfinity.tensorUnitPowerIso_split,
      `SerrePositivity.EInfinity.tensorCoInsertionAction_unit,
      `SerrePositivity.EInfinity.Operad.unitCoaction_equivariance,
      `SerrePositivity.EInfinity.Operad.unitCoaction_unit,
      `SerrePositivity.EInfinity.Operad.unitCoaction_partialComposition,
      `SerrePositivity.EInfinity.Operad.unitCoalgebra,
      `SerrePositivity.EInfinity.Operad.Algebra.isoOfCarrierIso,
      `SerrePositivity.EInfinity.convolutionEvaluation_unit_source,
      `SerrePositivity.EInfinity.convolutionPowerEvaluation_unit_source,
      `SerrePositivity.EInfinity.Operad.convolutionUnitIso,
      `SerrePositivity.EInfinity.Operad.convolutionUnitNatIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.endpointHom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.contractionHom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraPathFunctor,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_hom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat_hom,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.prepathAlgebra,
      `SerrePositivity.EInfinity.projectiveCofibration_degreewise_isSplitMono,
      `SerrePositivity.EInfinity.homPrecompose_degreewise_surjective,
      `SerrePositivity.EInfinity.homPrecompose_projectiveFibration,
      `SerrePositivity.EInfinity.homBiprodRestriction,
      `SerrePositivity.EInfinity.homBiprodRestriction_degreewise_surjective,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_eq_boundary,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluationPair_projectiveFibration,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationPair_projectiveFibration,
      `SerrePositivity.EInfinity.projectiveCofibrant_sphere,
      `SerrePositivity.EInfinity.projectiveCofibrant_unit,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.endpoint_false_cofibration,
      `SerrePositivity.EInfinity.projectiveTrivialCofibration_llp,
      `SerrePositivity.EInfinity.projectiveTrivialCofibration_homotopyEquiv,
      `SerrePositivity.EInfinity.homPrecomposeHomotopy,
      `SerrePositivity.EInfinity.homPrecomposeHomotopyEquiv,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.constant_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.evaluation_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraConstantNat_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.algebraEvaluationNat_quasiIso,
      `SerrePositivity.EInfinity.tensorInsertionBlock_naturality,
      `SerrePositivity.EInfinity.tensorInsertionAction_base_naturality,
      `SerrePositivity.EInfinity.Operad.Algebra.ofJointlyMonicActions,
      `SerrePositivity.EInfinity.Operad.Algebra.binaryProduct,
      `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIsLimit,
      `SerrePositivity.EInfinity.Operad.Algebra.binaryProductIso,
      `SerrePositivity.EInfinity.Operad.Algebra.terminalAlgebraIsTerminal,
      `SerrePositivity.EInfinity.Operad.Algebra.weakEquivalenceStructure,
      `SerrePositivity.EInfinity.Operad.Algebra.fibrationStructure,
      `SerrePositivity.EInfinity.Operad.Algebra.toTerminal_projectiveFibration,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.prepathAlgebra_p_compare,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.pathAlgebra_isGood,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.exists_retraction_path,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.fibrations_llp_quasiIso,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_rlp,
      `SerrePositivity.EInfinity.Operad.CoalgebraInterval.freeGeneratingTrivialCofibrations_llp_le,
      Lean.Name.str `SerrePositivity.EInfinity.Operad.CoalgebraInterval
        "freeGeneratingTrivialCofibrations_cell_acyclicity",
      `SerrePositivity.EInfinity.Operad.Algebra.forget_reflectsIsomorphisms,
      `SerrePositivity.EInfinity.Operad.Algebra.ofLimitCone,
      `SerrePositivity.EInfinity.Operad.Algebra.algebraLimitIsLimit,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsLimit,
      `SerrePositivity.EInfinity.tensorPower_preservesSiftedColimits_of_tensor,
      `SerrePositivity.EInfinity.tensorPower_preservesSiftedColimits,
      `SerrePositivity.EInfinity.schurFunctor_preservesSiftedColimits,
      `SerrePositivity.EInfinity.schurFunctor_preservesFilteredColimits,
      `SerrePositivity.EInfinity.Operad.freeAlgebraForget_preservesSiftedColimits,
      `SerrePositivity.EInfinity.Operad.freeAlgebraForget_preservesFilteredColimits,
      `SerrePositivity.EInfinity.Operad.Algebra.ofJointlyEpicActions,
      `SerrePositivity.EInfinity.Operad.Algebra.ofColimitCocone,
      `SerrePositivity.EInfinity.Operad.Algebra.algebraColimitIsColimit,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsColimit,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsSiftedColimitsOfShape,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_createsFilteredColimitsOfShape,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_monadic,
      `SerrePositivity.EInfinity.walkingReflexivePair_isSifted,
      `SerrePositivity.EInfinity.Operad.Algebra.hasReflexiveCoequalizers,
      `SerrePositivity.EInfinity.Operad.Algebra.diagramForget_monadic,
      `SerrePositivity.EInfinity.Operad.Algebra.forget_isCardinalAccessible,
      `SerrePositivity.EInfinity.Operad.freeAlgebra_finitelyPresentable,
      `SerrePositivity.EInfinity.Operad.freeGeneratingCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.Operad.freeGeneratingTrivialCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_weakEquivalences,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_fibrations,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_cofibrantlyGenerated,
      `SerrePositivity.EInfinity.Operad.intervalModelCategory_forget_isRightQuillen,
      `SerrePositivity.EInfinity.Surjection.BasisWord,
      `SerrePositivity.EInfinity.Surjection.degreeZeroEquiv,
      `SerrePositivity.EInfinity.Surjection.barrattEcclesWord_action,
      `SerrePositivity.EInfinity.Surjection.card_caesuras_basisWord,
      `SerrePositivity.EInfinity.Surjection.deletionCoefficient_final,
      `SerrePositivity.EInfinity.Surjection.representation,
      `SerrePositivity.EInfinity.Surjection.differential_basis,
      `SerrePositivity.EInfinity.Surjection.differential_renameLinear,
      `SerrePositivity.EInfinity.Surjection.listGenerator_ofFn,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_length,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_map,
      `SerrePositivity.EInfinity.TableReduction.output_length,
      `SerrePositivity.EInfinity.TableReduction.onSequence_action,
      `SerrePositivity.EInfinity.TableReduction.onSequence_degree_zero,
      `SerrePositivity.EInfinity.TableReduction.onSequence_nullary_zero,
      `SerrePositivity.EInfinity.TableReduction.onSequence_nullary_succ,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_basis,
      `SerrePositivity.EInfinity.TableReduction.available_after_take,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_same_adjacent_not_isChain,
      `SerrePositivity.EInfinity.Surjection.listGenerator_eq_zero_of_not_isChain,
      `SerrePositivity.EInfinity.TableReduction.output_not_isChain_of_adjacent_eq,
      `SerrePositivity.EInfinity.TableReduction.onSequence_eq_zero_of_adjacent_eq,
      `SerrePositivity.EInfinity.TableReduction.onSequence_eq_zero_of_degenerate,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_generator,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_action,
      `SerrePositivity.EInfinity.Surjection.firstOccurrences_nodup,
      `SerrePositivity.EInfinity.Surjection.caesuraList_eq_sort,
      `SerrePositivity.EInfinity.Surjection.rowStart_strictMono,
      `SerrePositivity.EInfinity.Surjection.rowStart_lt_length]

@[noinline] private def e2RequiredBatch5 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.TableReduction.canonicalRow_nodup,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_word_length,
      `SerrePositivity.EInfinity.TableReduction.canonicalPermutation_inv_list,
      `SerrePositivity.EInfinity.TableReduction.canonicalSimplex,
      `SerrePositivity.EInfinity.TableReduction.rows_canonicalVertices,
      `SerrePositivity.EInfinity.Surjection.firstOccurrences_cons,
      `SerrePositivity.EInfinity.Surjection.caesura_iff_mem_drop,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_succ_of_not_mem,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_exists_move,
      `SerrePositivity.EInfinity.TableReduction.canonicalRow_eq_of_final_interval,
      `SerrePositivity.EInfinity.Surjection.not_caesura_between_start_and_cut,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_adjacent_exists_move,
      `SerrePositivity.EInfinity.TableReduction.canonicalVertices_ne_adjacent,
      `SerrePositivity.EInfinity.TableReduction.canonicalSimplex_mem_nonDegenerate,
      `SerrePositivity.EInfinity.TableReduction.canonicalNondegenerateSimplex,
      `SerrePositivity.EInfinity.TableReduction.available_moved_wrong_cut_head,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_forces_move_length,
      `SerrePositivity.EInfinity.TableReduction.pastFinals_eq_append_segment,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_force_length,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_extract_original_segment,
      `SerrePositivity.EInfinity.TableReduction.canonicalRows_exclusion_update,
      `SerrePositivity.EInfinity.Surjection.not_caesura_after_last_start,
      `SerrePositivity.EInfinity.TableReduction.available_canonicalRow_last,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_canonical_last,
      `SerrePositivity.EInfinity.TableReduction.canonicalLengths_sum,
      `SerrePositivity.EInfinity.TableReduction.canonicalSchedule,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_canonical,
      `SerrePositivity.EInfinity.TableReduction.schedule_eq_canonical_of_isChain,
      `SerrePositivity.EInfinity.TableReduction.onSequence_canonical,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_comp_section,
      `SerrePositivity.EInfinity.TableReduction.degreeMap_surjective,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_surjective,
      `SerrePositivity.EInfinity.Surjection.deletionCoefficient_adjacent_eq,
      `SerrePositivity.EInfinity.Surjection.erase_adjacent_eq,
      `SerrePositivity.EInfinity.Surjection.rawDifferential_eq_zero_of_not_nondegenerate,
      `SerrePositivity.EInfinity.Surjection.differential_generator,
      `SerrePositivity.EInfinity.Surjection.differential_listGenerator,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_d_generator,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_comm_iff_vertexBoundary,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence_nullary,
      `SerrePositivity.EInfinity.TableReduction.transferUnit_inverse,
      `SerrePositivity.EInfinity.TableReduction.scheduleTransfer,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_delete_singleton,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace,
      `SerrePositivity.EInfinity.TableReduction.extractionTrace_of_reduceRows,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.removed_not_mem_output,
      `SerrePositivity.EInfinity.TableReduction.separatedRows_of_reduction,
      `SerrePositivity.EInfinity.Surjection.card_caesuras_ge,
      `SerrePositivity.EInfinity.TableReduction.recurrentEnds_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.rowEnds_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.rowEnds_caesura_iff,
      `SerrePositivity.EInfinity.Surjection.caesuraRank_caesuraAt,
      `SerrePositivity.EInfinity.TableReduction.rowEndSigns_of_reduction,
      `SerrePositivity.EInfinity.Surjection.caesuraRank_raw_get,
      `SerrePositivity.EInfinity.Surjection.deletionCoefficient_raw_get,
      `SerrePositivity.EInfinity.TableReduction.rawRowEndSigns_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.rowEndOffsets_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.singletonScheduleEquiv,
      `SerrePositivity.EInfinity.TableReduction.rows_scheduleDelete,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_deleted_vertex,
      `SerrePositivity.EInfinity.TableReduction.deletionCoefficient_schedule_rowEnd,
      `SerrePositivity.EInfinity.TableReduction.deletionCoefficient_singleton_final,
      `SerrePositivity.EInfinity.TableReduction.deletionCoefficient_singleton,
      `SerrePositivity.EInfinity.TableReduction.singleton_boundary_certificate,
      `SerrePositivity.EInfinity.TableReduction.rows_prefix_budget,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_inserted_vertex,
      `SerrePositivity.EInfinity.TableReduction.singleton_reduction_none_iff,
      `SerrePositivity.EInfinity.TableReduction.singleton_deletion_term,
      `SerrePositivity.EInfinity.TableReduction.sum_singletonSchedules_vertexBoundary,
      `SerrePositivity.EInfinity.Surjection.listDeletionTerm,
      `SerrePositivity.EInfinity.Surjection.rawListDifferential_eq_sum,
      `SerrePositivity.EInfinity.TableReduction.scheduleOffset_strictMono,
      `SerrePositivity.EInfinity.TableReduction.outputPosition_injective,
      `SerrePositivity.EInfinity.TableReduction.singletonPositions,
      `SerrePositivity.EInfinity.TableReduction.sum_singletonPositions,
      `SerrePositivity.EInfinity.TableReduction.rawListDifferential_partition,
      `SerrePositivity.EInfinity.TableReduction.remainderTerm,
      `SerrePositivity.EInfinity.TableReduction.differential_term_partition,
      `SerrePositivity.EInfinity.TableReduction.sum_singleton_terms_vertexBoundary,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence_vertexBoundary_add_remainder,
      `SerrePositivity.EInfinity.TableReduction.vertexBoundary_identity_iff_remainder_zero,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_comm_iff_remainder_zero,
      `SerrePositivity.EInfinity.TableReduction.schedule_excess_sum,
      `SerrePositivity.EInfinity.TableReduction.schedule_receiver_lt,
      `SerrePositivity.EInfinity.TableReduction.deletionScheduleTransfer,
      `SerrePositivity.EInfinity.TableReduction.deletionScheduleTransfer_inverse,
      `SerrePositivity.EInfinity.TableReduction.flatten_position_decomposition,
      `SerrePositivity.EInfinity.TableReduction.previous_position_lt_row_start,
      `SerrePositivity.EInfinity.TableReduction.row_lt_of_end_lt_start,
      `SerrePositivity.EInfinity.TableReduction.previousOccurrence_scheduleEnd,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_coefficient_receiver,
      `SerrePositivity.EInfinity.TableReduction.output_position_owner,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_rows,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_congr_removed,
      `SerrePositivity.EInfinity.TableReduction.donor_selected_split,
      `SerrePositivity.EInfinity.TableReduction.donor_exclusion_equiv,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_donor_step,
      `SerrePositivity.EInfinity.TableReduction.intermediate_selected_eq,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix,
      `SerrePositivity.EInfinity.TableReduction.extractionPrefix_of_reduceRows,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.early_exclusion,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.append_early_exclusion,
      `SerrePositivity.EInfinity.TableReduction.receiver_capacity_of_tail,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_receiver_step,
      `SerrePositivity.EInfinity.TableReduction.transfer_block_extraction,
      `SerrePositivity.EInfinity.TableReduction.transfer_block_deleted_outputs,
      `SerrePositivity.EInfinity.Surjection.previousOccurrence_no_between,
      `SerrePositivity.EInfinity.Surjection.previousOccurrence_not_mem_slice,
      `SerrePositivity.EInfinity.TableReduction.rows_deletionScheduleTransfer,
      `SerrePositivity.EInfinity.TableReduction.ofFn_split_two,
      `SerrePositivity.EInfinity.TableReduction.rows_transfer_blocks,
      `SerrePositivity.EInfinity.TableReduction.two_row_extraction,
      `SerrePositivity.EInfinity.TableReduction.rows_prefix_sum,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_location,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_row_cases,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_terminal_donor_step,
      `SerrePositivity.EInfinity.TableReduction.terminal_transfer_block_deleted_outputs,
      `SerrePositivity.EInfinity.TableReduction.scheduleBlock_nonempty,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.receiver_end_value,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.donor_value,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.previousOccurrence_not_mem_middle,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.donor_split,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.receiver_capacity,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.lift_transfer,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_transfer,
      `SerrePositivity.EInfinity.TableReduction.final_deletion_pair,
      `SerrePositivity.EInfinity.TableReduction.scheduleEnd_not_singleton]

@[noinline] private def e2RequiredBatch6 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.TableReduction.residual_caesura_row,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_released_donor_step,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.finish_length,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.finish_nodup,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.trans,
      `SerrePositivity.EInfinity.TableReduction.available_vertexRow_length_add,
      `SerrePositivity.EInfinity.TableReduction.available_vertexRow_release_length,
      `SerrePositivity.EInfinity.TableReduction.released_value_mem_extended_take,
      `SerrePositivity.EInfinity.TableReduction.before_last_excess,
      `SerrePositivity.EInfinity.TableReduction.last_row_available_length,
      `SerrePositivity.EInfinity.TableReduction.final_prefix_saturated,
      `SerrePositivity.EInfinity.TableReduction.CompleteRows,
      `SerrePositivity.EInfinity.TableReduction.completeRows_rows,
      `SerrePositivity.EInfinity.TableReduction.released_state_step,
      `SerrePositivity.EInfinity.TableReduction.ReleaseSearch,
      `SerrePositivity.EInfinity.TableReduction.releaseSearch_exists,
      `SerrePositivity.EInfinity.TableReduction.ReleaseSearch.toPrefix,
      `SerrePositivity.EInfinity.TableReduction.ReleaseSearch.unique,
      `SerrePositivity.EInfinity.TableReduction.released_suffix_budget,
      `SerrePositivity.EInfinity.TableReduction.releaseSearch_on_schedule_suffix,
      `SerrePositivity.EInfinity.TableReduction.releaseSearch_constructs_extension,
      `SerrePositivity.EInfinity.TableReduction.receiver_release,
      `SerrePositivity.EInfinity.TableReduction.reverse_block_extraction,
      `SerrePositivity.EInfinity.TableReduction.nonfinalRowPrefix_nonempty,
      `SerrePositivity.EInfinity.TableReduction.reverseTransferData_nonempty,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.split_success,
      `SerrePositivity.EInfinity.TableReduction.previousOccurrence_double_insert,
      `SerrePositivity.EInfinity.TableReduction.position_in_long_row_not_singleton,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.shortened_end,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_not_caesura,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_previousOccurrence,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_coefficient,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.pair_cancel,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_in_late_row,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.point_not_singleton,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.forward_rows,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.forward_schedule,
      `SerrePositivity.EInfinity.TableReduction.ReverseTransferData.forward_position,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.unique,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.prepend_releaseSearch,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.forward_release_search,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.reverse_search,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.reverse_result,
      `SerrePositivity.EInfinity.TableReduction.DeletionPoint,
      `SerrePositivity.EInfinity.TableReduction.deletionEquiv,
      `SerrePositivity.EInfinity.TableReduction.backward_forwardDeletion,
      `SerrePositivity.EInfinity.TableReduction.forward_backwardDeletion,
      `SerrePositivity.EInfinity.TableReduction.sum_remainingValue_zero,
      `SerrePositivity.EInfinity.TableReduction.sum_remainderTerm_eq_points,
      `SerrePositivity.EInfinity.TableReduction.sum_remainderTerm_zero,
      `SerrePositivity.EInfinity.TableReduction.differential_onSequence_eq_vertexBoundary,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_comm,
      `SerrePositivity.EInfinity.TableReduction.differential_comp_differential,
      `SerrePositivity.EInfinity.Surjection.normalizedChains,
      `SerrePositivity.EInfinity.TableReduction.chainMap,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.start_add_length_le,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.position_covered,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.value_mem_segments,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_strictMono,
      `SerrePositivity.EInfinity.Surjection.substitute_length,
      `SerrePositivity.EInfinity.Surjection.compositeWord_length,
      `SerrePositivity.EInfinity.Surjection.compositeWord_surjective,
      `SerrePositivity.EInfinity.Surjection.compositionExponent,
      `SerrePositivity.EInfinity.Surjection.compositionSign,
      `SerrePositivity.EInfinity.Surjection.compositionOnWords,
      `SerrePositivity.EInfinity.Surjection.partialComposition,
      `SerrePositivity.EInfinity.Surjection.partialComposition_basis,
      `SerrePositivity.EInfinity.Surjection.compositionOnWords_nullary_of_count_ne_one,
      `SerrePositivity.EInfinity.Surjection.substitute_isChain,
      `SerrePositivity.EInfinity.Surjection.compositeWord_nondegenerate,
      `SerrePositivity.EInfinity.Surjection.compositeBasisWord,
      `SerrePositivity.EInfinity.Surjection.compositeGenerator_eq_basis,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.boundary_mono,
      `SerrePositivity.EInfinity.Surjection.lineRank_last,
      `SerrePositivity.EInfinity.Surjection.sum_segmentDegree,
      `SerrePositivity.EInfinity.Surjection.sum_outerSegmentDegree,
      `SerrePositivity.EInfinity.Surjection.sum_outerSegmentDegree_suffix,
      `SerrePositivity.EInfinity.Surjection.compositionExponent_eq_component_exchanges,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_sign,
      `SerrePositivity.EInfinity.Surjection.DegreePath.blocks_sign,
      `SerrePositivity.EInfinity.Surjection.compositionPath,
      `SerrePositivity.EInfinity.Surjection.compositionPath_blockExponent,
      `SerrePositivity.EInfinity.Surjection.compositionPath_sign,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_inverse_row,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_inverse_row_substitute,
      `SerrePositivity.EInfinity.Surjection.remaining_mem_compositionRemoved,
      `SerrePositivity.EInfinity.Surjection.inserted_mem_compositionRemoved,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_available_substitute,
      `SerrePositivity.EInfinity.Surjection.compositionStateRemoved,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_state_available_substitute,
      `SerrePositivity.EInfinity.Surjection.compositionStateRemoved_update,
      `SerrePositivity.EInfinity.Surjection.compositionStateRemoved_finalize,
      `SerrePositivity.EInfinity.Surjection.compositionSelectedUpdate_before,
      `SerrePositivity.EInfinity.Surjection.compositionSelectedUpdate_inside,
      `SerrePositivity.EInfinity.Surjection.compositionSelectedUpdate_after,
      `SerrePositivity.EInfinity.Surjection.compositionExtractionStep_before,
      `SerrePositivity.EInfinity.Surjection.compositionExtractionStep_inside,
      `SerrePositivity.EInfinity.Surjection.compositionExtractionStep_after,
      `SerrePositivity.EInfinity.Surjection.lineRank_eq_rawCaesura_count,
      `SerrePositivity.EInfinity.TableReduction.rowEndPositions_count_before_in_row,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.lineRank_in_row,
      `SerrePositivity.EInfinity.TableReduction.lineRank_schedule_of_reduction,
      `SerrePositivity.EInfinity.TableReduction.reductionRow,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_bounds,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_eq_iff,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_mono,
      `SerrePositivity.EInfinity.Surjection.segmentDegree_eq_reductionRows,
      `SerrePositivity.EInfinity.Surjection.outerSegmentDegree_eq_reductionRows,
      `SerrePositivity.EInfinity.TableReduction.reductionRow_lt_of_repeat,
      `SerrePositivity.EInfinity.TableReduction.occurrence_reductionRow_strictMono,
      `SerrePositivity.EInfinity.TableReduction.scheduleRowCursor_nonempty,
      `SerrePositivity.EInfinity.TableReduction.reductionColumn_position,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.reductionColumn_value,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.available_slot_split,
      `SerrePositivity.EInfinity.TableReduction.reductionCursor_composite_row,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.unique,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.next_state,
      `SerrePositivity.EInfinity.TableReduction.ScheduleRowCursor.remainder_success_eq_drop,
      `SerrePositivity.EInfinity.TableReduction.rowInterval_prefix,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.interval_prefix_word,
      `SerrePositivity.EInfinity.TableReduction.ScheduleBlock.interval_source_rows,
      `SerrePositivity.EInfinity.TableReduction.cursorInterval_nonempty,
      `SerrePositivity.EInfinity.TableReduction.reductionInterval_nonempty,
      `SerrePositivity.EInfinity.TableReduction.ReductionInterval.success,
      `SerrePositivity.EInfinity.Surjection.componentExtraction_word,
      `SerrePositivity.EInfinity.Surjection.componentExtraction_length,
      `SerrePositivity.EInfinity.Surjection.componentExtraction_success]

@[noinline] private def e2RequiredBatch7 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Surjection.componentExtraction_adjacent_prefix,
      `SerrePositivity.EInfinity.Surjection.outerComponentExtraction_success,
      `SerrePositivity.EInfinity.Surjection.verticalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.ReductionInterval.permutationRows_eq,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_available_slot,
      `SerrePositivity.EInfinity.Surjection.componentVerticalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_removed_eq,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_word_eq,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_of_success,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.not_mem_initial,
      `SerrePositivity.EInfinity.Surjection.substitute_head_prefix,
      `SerrePositivity.EInfinity.Surjection.horizontalLabel_state_update,
      `SerrePositivity.EInfinity.Surjection.horizontalExtractionStep_success,
      `SerrePositivity.EInfinity.Surjection.horizontalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_available_head,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_not_mem,
      `SerrePositivity.EInfinity.Surjection.componentHorizontalExtraction_success,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_last_singleton,
      `SerrePositivity.EInfinity.Surjection.horizontalLabel_injective,
      `SerrePositivity.EInfinity.Surjection.substitute_singleton_nodup,
      `SerrePositivity.EInfinity.Surjection.horizontalLabel_singleton_state_update,
      `SerrePositivity.EInfinity.Surjection.singletonHorizontalExtraction_success,
      `SerrePositivity.EInfinity.Surjection.finalHorizontalExtraction_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.raw_success_zero,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fused_success_zero,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedWord_step,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fused_success_blockWord,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedWord_eq_blockWord,
      `SerrePositivity.EInfinity.Surjection.substitute_append,
      `SerrePositivity.EInfinity.Surjection.substitute_at_occurrence,
      `SerrePositivity.EInfinity.Surjection.compositeWord_at_occurrence,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.firstHorizontal_dropLast,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.middleHorizontal_dropLast,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.finalHorizontal_word,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.verticalWord_append_endpoint,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.blockWord_eq_compositeWord,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fused_success_compositeWord,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedRows_length,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedSchedule,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.rows_fusedSchedule_of_fst,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.horizontalRows_fst,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.verticalRows_fst,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedRows_fst_step,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_horizontal_front,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_horizontal_back,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_vertical_front,
      `SerrePositivity.EInfinity.Surjection.DegreePath.append_vertical_back,
      `SerrePositivity.EInfinity.Surjection.DegreePath.vertices_append,
      `SerrePositivity.EInfinity.Surjection.DegreePath.vertices_blocks,
      `SerrePositivity.EInfinity.Surjection.compositionPath_vertices,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.rowAtGrid_valid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.horizontalRows_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.verticalRows_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedRows_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.pathSequence_rows_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.pathSequence_success_of_vertices,
      `SerrePositivity.EInfinity.Surjection.DegreePath.walkVertices_eq_blocks,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.compositionPath_vertices_eq_grid,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.rows_pathSequence,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.pathSequence_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.term_shuffleSimplex,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.signed_term_shuffleSimplex,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerWord_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.inner_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerWord_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.input_words_unique,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.splitParts_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.partition_unique,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.partsOfWord_compositeWord,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.composite_data_injective,
      `SerrePositivity.EInfinity.TableReduction.schedule_eq_of_same_output,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_reordered_endpoint_not_isChain,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_block_endpoint_mem_middle,
      `SerrePositivity.EInfinity.TableReduction.available_block_next_head_mem_middle,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_endpoint_inserted,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_next_head_inserted,
      `SerrePositivity.EInfinity.TableReduction.available_filterMap,
      `SerrePositivity.EInfinity.TableReduction.filterMap_selection_retained_last,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.filterMap,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerLabel_available_composition_row,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_inner_step,
      `SerrePositivity.EInfinity.Surjection.vertical_prefix_inner_projection,
      `SerrePositivity.EInfinity.Surjection.vertical_prefix_inner_rows,
      `SerrePositivity.EInfinity.TableReduction.filterMap_selection_discarded_last,
      `SerrePositivity.EInfinity.TableReduction.filterMap_final_prefix,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_vertical_inner_pair,
      `SerrePositivity.EInfinity.Surjection.vertical_interval_final_inner_nonempty,
      `SerrePositivity.EInfinity.Surjection.vertical_interval_inner_projection,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recovered_state_mem,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recovered_available_substitute,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerRemoved_nil,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerRemoved_subset,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerLabel_available_composition_row,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_take_prefix,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_drop_rank,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_take,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_bounds,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_update_mem,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_step,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outer_table_success,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_collapse,
      `SerrePositivity.EInfinity.TableReduction.compressRows_fst,
      `SerrePositivity.EInfinity.TableReduction.compressRows_success,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_flatten,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.compressed_outer_table_success,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_boundary_ne,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_horizontal_inner_boundary_eq,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_horizontal_outer_boundary_ne,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerSelection_nodup,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.horizontal_outer_selections_isChain,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_isChain_of_tail,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.compress_isChain,
      `SerrePositivity.EInfinity.TableReduction.extractionTrace_of_lengths,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recoveredOuterTable_trace,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recoveredOuterTable_separated,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.compressed_outer_table_nondegenerate,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_ofFn_orderHom,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffleTableEntries_axis,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_recovery,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_compressed_outer_rows,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_isChain_of_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_isChain_of_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_recovery_with_rows,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffleSimplex_outer_recovery,
      `SerrePositivity.EInfinity.TableReduction.output_covers,
      `SerrePositivity.EInfinity.TableReduction.schedule_of_table,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_excess,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_schedule]

@[noinline] private def e2RequiredBatch8 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_outer_basis,
      `SerrePositivity.EInfinity.TableReduction.ConsumptionPrefix.normalize,
      `SerrePositivity.EInfinity.TableReduction.ConsumptionPrefix.close_of_prefix,
      `SerrePositivity.EInfinity.TableReduction.ConsumptionPrefix.reduction,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.filterMap_consumption,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_consumption,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_close,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_before_vertical,
      `SerrePositivity.EInfinity.Surjection.horizontal_inner_success,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_isChain,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_append_of_separated,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerWord_append_of_retained,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerRunDecomposition_exists,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.InnerRunDecomposition.sources_eq,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.vertical_inner_join,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.inner_table_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.innerWord_covers,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_recovery_with_rows,
      `SerrePositivity.EInfinity.TableReduction.ExtractionPrefix.recurrent_tail,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.recurrent_of_schedule,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.InnerRunDecomposition.inner_recurrent,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.inner_recurrent_table_success,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_schedule,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_inner_basis,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.collapse_append_length,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.shared_endpoints_of_saturated,
      `SerrePositivity.EInfinity.Surjection.AdjacentCollapse.shared_rows_take,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.ofRows,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.ofRows_segments,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.existsUnique_of_rows,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.outerWord_remaining_cons,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.exists_nonempty_parts,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.splitParts_properties,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.recovered_partition_existsUnique,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_source_partition,
      `SerrePositivity.EInfinity.TableReduction.schedule_eq_of_same_list,
      `SerrePositivity.EInfinity.TableReduction.selected_eq_of_same_output,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.vertical_inserted_join,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.horizontal_not_inserted_join,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.boundaryInserted_iff_notMem,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shufflePath_eq_of_same_output,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.compositionPath_eq_of_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.fusedSchedule_eq_of_success,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.eq_of_same_output,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.shuffle_reconstruction_existsUnique,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.equiv,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sourceFintype,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.forward_term,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.signedTerm_eq_zero_of_not_successful,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sum_all_eq_source,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sum_onSequence_eq_source,
      `SerrePositivity.EInfinity.TableReduction.word_exists_of_success,
      `SerrePositivity.EInfinity.TableReduction.term_eq_sum_words,
      `SerrePositivity.EInfinity.TableReduction.onSequence_eq_sum_successfulWords,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.wordsEquiv,
      `SerrePositivity.EInfinity.Surjection.CompositionSuccess.sum_source_eq_partialComposition,
      `SerrePositivity.EInfinity.TableReduction.onSequence_partialComposition_of_pos,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffle_generators_of_pos,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffleBilinear_of_pos,
      `SerrePositivity.EInfinity.TableReduction.onSequence_shuffle_nullary_succ,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffleBilinear_nullary_succ,
      `SerrePositivity.EInfinity.Surjection.substitute_nullary,
      `SerrePositivity.EInfinity.Surjection.eraseSlotLabel_partial_injective,
      `SerrePositivity.EInfinity.Surjection.eraseSlotWord_length,
      `SerrePositivity.EInfinity.Surjection.permutationComposition_inverse_row_nullary,
      `SerrePositivity.EInfinity.Surjection.compositionOnWords_nullary_of_count_eq_one,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_filterMap_of_discarded_mem,
      `SerrePositivity.EInfinity.TableReduction.permutationComposition_nullary_available,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_eraseSlotWord_of_mem,
      `SerrePositivity.EInfinity.TableReduction.rows_nullary,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_nullary,
      `SerrePositivity.EInfinity.TableReduction.completeRows_nullarySourceRows,
      `SerrePositivity.EInfinity.TableReduction.nullary_success_extension,
      `SerrePositivity.EInfinity.TableReduction.nullary_success_schedule,
      `SerrePositivity.EInfinity.Surjection.isChain_insert_of_eraseSlotWord,
      `SerrePositivity.EInfinity.TableReduction.nullary_successfulWord_lift_exists,
      `SerrePositivity.EInfinity.TableReduction.nullary_successfulWord_lift_term,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.filterMap_reduceRows,
      `SerrePositivity.EInfinity.TableReduction.recurrentEnds_eraseSlotWord_ready,
      `SerrePositivity.EInfinity.TableReduction.nullary_forward_schedule,
      `SerrePositivity.EInfinity.TableReduction.nullary_successfulWord_forward_exists,
      `SerrePositivity.EInfinity.TableReduction.nullarySourceFintype,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_word,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_surjective,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_term,
      `SerrePositivity.EInfinity.TableReduction.take_length_eq_of_filterMap_eq,
      `SerrePositivity.EInfinity.TableReduction.ExtractionTrace.eq_of_filterMap,
      `SerrePositivity.EInfinity.TableReduction.nullary_projected_selected_eq,
      `SerrePositivity.EInfinity.TableReduction.nullary_success_output_unique,
      `SerrePositivity.EInfinity.TableReduction.nullaryForward_injective,
      `SerrePositivity.EInfinity.TableReduction.nullarySuccessEquiv,
      `SerrePositivity.EInfinity.TableReduction.sum_nullary_source_eq_target,
      `SerrePositivity.EInfinity.TableReduction.sum_nullary_all_eq_source,
      `SerrePositivity.EInfinity.TableReduction.onSequence_partialComposition_nullary_zero,
      `SerrePositivity.EInfinity.TableReduction.onSequence_partialComposition,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffle_generators,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_shuffleBilinear,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_degreeTransport,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_arityTransport,
      `SerrePositivity.EInfinity.Surjection.partialComposition_d_positive,
      `SerrePositivity.EInfinity.Surjection.partialComposition_d_leftZero,
      `SerrePositivity.EInfinity.Surjection.partialComposition_d_rightZero,
      `SerrePositivity.EInfinity.Surjection.unitElement,
      `SerrePositivity.EInfinity.Surjection.partialComposition_left_unit,
      `SerrePositivity.EInfinity.Surjection.partialComposition_right_unit,
      `SerrePositivity.EInfinity.Surjection.partialComposition_nested_assoc,
      `SerrePositivity.EInfinity.Surjection.partialComposition_parallel_assoc,
      `SerrePositivity.EInfinity.TableReduction.normalizedMap_rightAction,
      `SerrePositivity.EInfinity.Surjection.partialComposition_inner_rightAction,
      `SerrePositivity.EInfinity.Surjection.partialComposition_outer_rightAction,
      `SerrePositivity.EInfinity.Surjection.complex,
      `SerrePositivity.EInfinity.Surjection.complexXIso,
      `SerrePositivity.EInfinity.Surjection.complex_isZero_positive,
      `SerrePositivity.EInfinity.Surjection.normalizedRename,
      `SerrePositivity.EInfinity.Surjection.complexRename,
      `SerrePositivity.EInfinity.Surjection.sequence,
      `SerrePositivity.EInfinity.TableReduction.cochainMap,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_f_surjective,
      `SerrePositivity.EInfinity.TableReduction.sequenceMap,
      `SerrePositivity.EInfinity.Surjection.cochainCompositionBilinear,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_f_surjective_int,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_compositionBilinear,
      `SerrePositivity.EInfinity.Surjection.cochainCompositionBilinear_d,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition,
      `SerrePositivity.EInfinity.Surjection.ι_complexPartialComposition,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_neg_tmul,
      `SerrePositivity.EInfinity.TableReduction.complexPartialComposition_comm]

@[noinline] private def e2RequiredBatch9 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Surjection.complexUnit,
      `SerrePositivity.EInfinity.Surjection.complexUnit_comm,
      `SerrePositivity.EInfinity.Surjection.complexUnit_zero_apply,
      `SerrePositivity.EInfinity.TableReduction.cochainMap_epi,
      `SerrePositivity.EInfinity.TableReduction.tensor_epi_of_epi,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_left_unit,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_right_unit,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_inner_rightAction,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_outer_rightAction,
      `SerrePositivity.EInfinity.TableReduction.triple_cochainMap_epi,
      `SerrePositivity.EInfinity.TableReduction.exchangeLastFactors_naturality,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_nested_assoc,
      `SerrePositivity.EInfinity.Surjection.complexPartialComposition_parallel_assoc,
      `SerrePositivity.EInfinity.Surjection.operad,
      `SerrePositivity.EInfinity.TableReduction.operadMap,
      `SerrePositivity.EInfinity.TableReduction.operadMap_app,
      `SerrePositivity.EInfinity.TableReduction.operadMap_f_surjective,
      `SerrePositivity.EInfinity.IntervalCuts.edge_degree_bound,
      `SerrePositivity.EInfinity.IntervalCuts.vertexNondegenerate_iff,
      `SerrePositivity.EInfinity.IntervalCuts.sum_edgeOutputDegree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign,
      `SerrePositivity.EInfinity.IntervalCuts.edgeValue,
      `SerrePositivity.EInfinity.IntervalCuts.vertexValue,
      `SerrePositivity.EInfinity.IntervalCuts.edgeLinear,
      `SerrePositivity.EInfinity.IntervalCuts.vertexLinear,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_total_degree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeValue_eq_zero_of_degree,
      `SerrePositivity.EInfinity.IntervalCuts.interval,
      `SerrePositivity.EInfinity.IntervalCuts.intervalXIso,
      `SerrePositivity.EInfinity.IntervalCuts.faceChain,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector,
      `SerrePositivity.EInfinity.IntervalCuts.edgeChain_d,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorOfDegree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_tupleDegree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_basis,
      `SerrePositivity.EInfinity.IntervalCuts.intervalChains_isZero,
      `SerrePositivity.EInfinity.IntervalCuts.interval_isZero_positive,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_edge_d,
      `SerrePositivity.EInfinity.IntervalCuts.tensorPair_d_apply,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector_d,
      `SerrePositivity.EInfinity.IntervalCuts.simplex_cases,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_vertex_d,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_edge_d_sub,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm_eq_zero_of_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector_d_eq_zero_of_vertices,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVector_d_eq_sum_edges,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm_zero_edge,
      `SerrePositivity.EInfinity.IntervalCuts.edgeNondegenerate_iff,
      `SerrePositivity.EInfinity.IntervalCuts.repeated_straddles,
      `SerrePositivity.EInfinity.IntervalCuts.caesura_before_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.edgePositionExponent_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_of_nondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions_card,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eq_edge_iff,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_tensorVector_d,
      `SerrePositivity.EInfinity.IntervalCuts.erase_edgeNondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.eraseCutBasisWord,
      `SerrePositivity.EInfinity.IntervalCuts.generator_erase_of_cut,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutputVertices_erase_of_ne,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eraseCut_left,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eraseCut_right,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount,
      `SerrePositivity.EInfinity.IntervalCuts.edgePermutationExponent_eq_inversionCount,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_eq_inversionCount,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_erase_balance,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionSign_erase,
      `SerrePositivity.EInfinity.IntervalCuts.positionRank_active_caesura,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_prefix_degree,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_caesura_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.deletionCoefficient_repeat_pair,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_final_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.caesura_erase_iff_of_cut,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions_erase_image_eq_erase,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_image,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_eq_removed,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_left_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_right_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_succ,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_natDegree,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_update_edge,
      `SerrePositivity.EInfinity.IntervalCuts.prefixDegree_succ,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_zero_cons,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_succ_cons,
      `SerrePositivity.EInfinity.IntervalCuts.tensorBoundaryTerm_eq_endpoints,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_eraseCut_left,
      `SerrePositivity.EInfinity.IntervalCuts.endpointTensor_eraseCut_right,
      `SerrePositivity.EInfinity.IntervalCuts.cut_factor_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.original_cut_iff_no_same_side_repeat,
      `SerrePositivity.EInfinity.IntervalCuts.CutDeletionDefect,
      `SerrePositivity.EInfinity.IntervalCuts.cutDeletionDefect_exists_iff,
      `SerrePositivity.EInfinity.IntervalCuts.cutDeletionDefect_unique,
      `SerrePositivity.EInfinity.IntervalCuts.erase_partner_edgeNondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.residual_partner_existsUnique,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_swap,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_ne,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swapEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_output,
      `SerrePositivity.EInfinity.IntervalCuts.residualCutBasisWord,
      `SerrePositivity.EInfinity.IntervalCuts.residualCut_output_family,
      `SerrePositivity.EInfinity.IntervalCuts.residualCut_tensor_eq,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionSign_erase_same_color,
      `SerrePositivity.EInfinity.IntervalCuts.caesura_erase_final,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_erase_final,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.pivot_not_caesura,
      `SerrePositivity.EInfinity.IntervalCuts.NonpivotResidualCut.swap_coefficient,
      `SerrePositivity.EInfinity.IntervalCuts.nonpivotResidualCut_weighted_sum,
      `SerrePositivity.EInfinity.IntervalCuts.residualCut_tensor_sum_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.edgeNondegenerate_between,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_pivot_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_pivot_endpoint_one,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_pivot_endpoint_zero,
      `SerrePositivity.EInfinity.IntervalCuts.pivotBoundary_gap_difference,
      `SerrePositivity.EInfinity.IntervalCuts.pivotBoundaryValue_sum,
      `SerrePositivity.EInfinity.IntervalCuts.pivotBoundaryValue_sum_zeroDegree,
      `SerrePositivity.EInfinity.IntervalCuts.GapNondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.gap_before_defect_existsUnique,
      `SerrePositivity.EInfinity.IntervalCuts.gap_after_defect_existsUnique,
      `SerrePositivity.EInfinity.IntervalCuts.erase_pivot_iff_gap_before,
      `SerrePositivity.EInfinity.IntervalCuts.erase_pivot_iff_gap_after]

@[noinline] private def e2RequiredBatch10 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.IntervalCuts.pivotEraseBasisWord,
      `SerrePositivity.EInfinity.IntervalCuts.pivotErase_tensor_before,
      `SerrePositivity.EInfinity.IntervalCuts.pivotErase_tensor_after,
      `SerrePositivity.EInfinity.IntervalCuts.positionRank_gap_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.caesuraRank_gap_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions_erase_final_pivot_image,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_coefficient_before,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_coefficient_after,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_weighted_before,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_weighted_after,
      `SerrePositivity.EInfinity.IntervalCuts.pivotDeletion_weighted_pair,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut.sum_split,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut.beforeEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.PivotResidualCut.afterEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.pivotResidualValue_sum,
      `SerrePositivity.EInfinity.IntervalCuts.gap_sum_complement,
      `SerrePositivity.EInfinity.IntervalCuts.pivotResidualValue_sum_eq_boundary,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.word,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.nonpivotEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.pivotEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.sum_three,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_reduce,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_eq_zero_of_no_cut,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.fiberEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NormalizedDeletedCut.sum_fibers,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_sum_subtype,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_generator,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_differentialOnWord,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_differentialOnWord_reduce,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_differentialOnWord_eq_zero_of_no_cut,
      `SerrePositivity.EInfinity.IntervalCuts.RepeatCutPair,
      `SerrePositivity.EInfinity.IntervalCuts.regularCutEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.RepeatCutPair.factorBoundary_eq_pair,
      `SerrePositivity.EInfinity.IntervalCuts.repeatPairFiberEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.normalizedDeletedValue_sum_regular,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_boundary_factors,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_d_positive,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_d_zero,
      `SerrePositivity.EInfinity.IntervalCuts.degreeOne_deletion_pair,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_generator_zero_degree,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_differentialOnWord,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponentOnWord_d_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponentOnWord_d_positive,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_d_positive,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_d_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_d_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_differential,
      `SerrePositivity.EInfinity.IntervalCuts.vertexChainLift,
      `SerrePositivity.EInfinity.IntervalCuts.edgeChainLift,
      `SerrePositivity.EInfinity.IntervalCuts.rawEdgeLift_degeneracies_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInputBilinear,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInputBilinear,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInputBilinear_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInputBilinear_edge,
      `SerrePositivity.EInfinity.IntervalCuts.zeroSimplex_eq_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.monoOneSimplex_eq_edge,
      `SerrePositivity.EInfinity.IntervalCuts.interval_generator_one_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexChain_hom_ext,
      `SerrePositivity.EInfinity.IntervalCuts.edgeChain_hom_ext,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInput_hom_ext,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInput_hom_ext,
      `SerrePositivity.EInfinity.IntervalCuts.cochainActionBilinear,
      `SerrePositivity.EInfinity.IntervalCuts.cochainActionComponent,
      `SerrePositivity.EInfinity.IntervalCuts.cochainActionBilinear_neg_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.cochainActionBilinear_neg_edge,
      `SerrePositivity.EInfinity.IntervalCuts.intervalInput_edge_d,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInputBilinear_d_eq_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInputBilinear_differential,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInputBilinear_d_positive,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInputBilinear_d_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInputBilinear_eq_zero_of_positive,
      `SerrePositivity.EInfinity.IntervalCuts.surjection_d_neg_apply,
      `SerrePositivity.EInfinity.IntervalCuts.interval_eq_zero_of_other,
      `SerrePositivity.EInfinity.IntervalCuts.cochainActionBilinear_d,
      `SerrePositivity.EInfinity.IntervalCuts.cochainActionComponent_d,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction,
      `SerrePositivity.EInfinity.IntervalCuts.ι_cochainAction,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_neg_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_neg_edge,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorOfDegree_one,
      `SerrePositivity.EInfinity.IntervalCuts.unitWord_edgeNondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.unitWord_edgeOutput,
      `SerrePositivity.EInfinity.IntervalCuts.unitWord_edgeSign,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_unitElement,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_unitElement,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_unit_input,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_unit_inv,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_unit,
      `SerrePositivity.EInfinity.IntervalCuts.edgeNondegenerate_rename_iff,
      `SerrePositivity.EInfinity.IntervalCuts.edgeFiber_rename,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutputVertices_rename,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_rename,
      `SerrePositivity.EInfinity.IntervalCuts.activePositions_rename,
      `SerrePositivity.EInfinity.IntervalCuts.edgePositionExponent_rename,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.swapFirstIso_apply,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_cons,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_cons,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_cons_cons,
      `SerrePositivity.EInfinity.IntervalCuts.swapFirstIso_tensorVectorAt,
      `SerrePositivity.EInfinity.IntervalCuts.cons_comp_shiftPerm,
      `SerrePositivity.EInfinity.IntervalCuts.adjacentIso_tensorVectorAt,
      `SerrePositivity.EInfinity.IntervalCuts.adjacentTransposition_val,
      `SerrePositivity.EInfinity.IntervalCuts.adjacentTransposition_order_change,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversions,
      `SerrePositivity.EInfinity.IntervalCuts.card_positionInversions,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversions_symmDiff_adjacent,
      `SerrePositivity.EInfinity.IntervalCuts.colorCrossPairs,
      `SerrePositivity.EInfinity.IntervalCuts.colorCrossPairs_subsingleton,
      `SerrePositivity.EInfinity.IntervalCuts.colorCrossPairs_nonempty_iff,
      `SerrePositivity.EInfinity.IntervalCuts.card_colorCrossPairs,
      `SerrePositivity.EInfinity.IntervalCuts.neg_one_pow_card_symmDiff,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionSign_adjacent,
      `SerrePositivity.EInfinity.IntervalCuts.edgeSign_adjacent,
      `SerrePositivity.EInfinity.IntervalCuts.edgeCut_tensor_adjacent,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_adjacent,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponentOnWord_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.vertexTensor_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponentOnWord_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInputBilinear_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInputBilinear_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.complexRename_neg_hom_apply]

@[noinline] private def e2RequiredBatch11 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.IntervalCuts.cochainActionBilinear_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_permutation,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_equivariance,
      `SerrePositivity.EInfinity.IntervalCuts.occurrenceCount_le_two_of_cut,
      `SerrePositivity.EInfinity.IntervalCuts.occurrenceCount_pivot_eq_one,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eq_edge_of_two_occurrences,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_eq_edge_iff_pivot_or_two,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutput_ne_edge_iff_single_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_compositionOnWords,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_compositionOnWords_positive,
      `SerrePositivity.EInfinity.IntervalCuts.compositionEdgeCutTerm,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_composition_cut_sum,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_partialComposition_edge_tmul,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCutValid,
      `SerrePositivity.EInfinity.IntervalCuts.decidableNestedEdgeCutValid,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.ofVertex,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.ofEdge,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.occurrenceCount_eq_one_or_two,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.occurrenceCount_eq_one_of_none,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.occurrenceCount_eq_two_of_some_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.partition,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.partition_of_none,
      `SerrePositivity.EInfinity.IntervalCuts.compositeWord_at_non_slot,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_value,
      `SerrePositivity.EInfinity.IntervalCuts.compositeBasisWord_outerPosition,
      `SerrePositivity.EInfinity.IntervalCuts.occurrenceAt_of_count_one,
      `SerrePositivity.EInfinity.IntervalCuts.segment_of_count_one,
      `SerrePositivity.EInfinity.IntervalCuts.segments_of_count_one,
      `SerrePositivity.EInfinity.IntervalCuts.compositeWord_at_single_slot,
      `SerrePositivity.EInfinity.IntervalCuts.compositeInnerPosition,
      `SerrePositivity.EInfinity.IntervalCuts.compositeInnerPosition_value,
      `SerrePositivity.EInfinity.IntervalCuts.cut_prefix_nodup,
      `SerrePositivity.EInfinity.IntervalCuts.cut_suffix_nodup,
      `SerrePositivity.EInfinity.IntervalCuts.cut_nondegenerate_of_nodup,
      `SerrePositivity.EInfinity.IntervalCuts.edgeNondegenerate_iff_list_nodup,
      `SerrePositivity.EInfinity.IntervalCuts.splice_take_inside,
      `SerrePositivity.EInfinity.IntervalCuts.splice_drop_inside,
      `SerrePositivity.EInfinity.IntervalCuts.splice_cut_nodup,
      `SerrePositivity.EInfinity.IntervalCuts.position_eq_of_count_one,
      `SerrePositivity.EInfinity.IntervalCuts.single_slot_not_mem_prefix,
      `SerrePositivity.EInfinity.IntervalCuts.single_slot_not_mem_suffix,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_no_slot_horizontalLabel_parts,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_nodup_of_no_slot,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_disjoint_inserted,
      `SerrePositivity.EInfinity.IntervalCuts.composite_single_slot_cut_nondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.compositeBasisWord_innerPosition,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_value,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_pivot_value,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_pivot_nondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_of_no_slot,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_disjoint_inserted_no_slot,
      `SerrePositivity.EInfinity.IntervalCuts.remaining_mem_substitute_iff,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_nodup_of_parts,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_take_at_non_slot,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_drop_at_non_slot,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_prefix,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_suffix,
      `SerrePositivity.EInfinity.IntervalCuts.composite_non_slot_cut_nondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.segments_cast_count,
      `SerrePositivity.EInfinity.IntervalCuts.two_partition_segments_nodup,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.partition_of_some_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.partition_segments_nodup_of_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_nondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_nondegenerate,
      `SerrePositivity.EInfinity.IntervalCuts.CompositeEdgeCut,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.toCompositeCut,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.exists_some_of_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_pivot_val,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.toCompositeCut_outer_injective,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.toCompositeCut_injective,
      `SerrePositivity.EInfinity.IntervalCuts.remaining_count_substitute,
      `SerrePositivity.EInfinity.IntervalCuts.composite_remaining_occurrenceCount,
      `SerrePositivity.EInfinity.IntervalCuts.outer_remaining_occurrenceCount_le_two,
      `SerrePositivity.EInfinity.IntervalCuts.outer_pivot_occurrenceCount_eq_one,
      `SerrePositivity.EInfinity.IntervalCuts.composite_pivot_eq_outerPosition,
      `SerrePositivity.EInfinity.IntervalCuts.exists_unique_outer_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.nodup_of_substitute_nodup,
      `SerrePositivity.EInfinity.IntervalCuts.outer_cut_nondegenerate_of_slot_counts,
      `SerrePositivity.EInfinity.IntervalCuts.outer_cut_nondegenerate_of_single_slot,
      `SerrePositivity.EInfinity.IntervalCuts.single_slot_cuts_nondegenerate_of_composite,
      `SerrePositivity.EInfinity.IntervalCuts.composite_single_slot_cut_nondegenerate_iff,
      `SerrePositivity.EInfinity.IntervalCuts.exists_single_slot_cuts_of_inserted_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_prefix_length_mono,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegmentPosition,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegmentPosition_value,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_prefix_length_at_occurrence,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegmentPosition_lt,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegmentFirst,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegmentLast,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegment_boundary_value,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegment_boundary_straddles,
      `SerrePositivity.EInfinity.IntervalCuts.slot_occurrenceCount_le_two_of_composite_cut,
      `SerrePositivity.EInfinity.IntervalCuts.exists_segmentPosition_of_inserted_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.slot_occurrenceCount_eq_one_of_inserted_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.exists_cuts_of_inserted_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.exists_preimage_of_inserted_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_lt_segmentFirst,
      `SerrePositivity.EInfinity.IntervalCuts.compositeSegmentLast_lt_outerPosition,
      `SerrePositivity.EInfinity.IntervalCuts.slot_counts_of_compositeOuterPosition_cut,
      `SerrePositivity.EInfinity.IntervalCuts.outer_cut_nondegenerate_of_compositeOuterPosition,
      `SerrePositivity.EInfinity.IntervalCuts.segment_nodup_of_same_side,
      `SerrePositivity.EInfinity.IntervalCuts.segment_nodup_of_last_le_cut,
      `SerrePositivity.EInfinity.IntervalCuts.segment_nodup_of_cut_le_first,
      `SerrePositivity.EInfinity.IntervalCuts.segment_cast_count,
      `SerrePositivity.EInfinity.IntervalCuts.inner_two_cut_nondegenerate_of_composite,
      `SerrePositivity.EInfinity.IntervalCuts.inner_degree_zero_of_single_slot_outer_cut,
      `SerrePositivity.EInfinity.IntervalCuts.exists_preimage_of_remaining_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.toCompositeCut_surjective,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositeCutEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_composition_nonzero_cut_sum,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_composition_nested_cut_sum,
      `SerrePositivity.EInfinity.IntervalCuts.zero_mem_edgeOutputVertices_iff_mem_take,
      `SerrePositivity.EInfinity.IntervalCuts.one_mem_edgeOutputVertices_iff_mem_drop,
      `SerrePositivity.EInfinity.IntervalCuts.edgeOutputVertices_eq_of_list_membership,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_remaining_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_eq_outer,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_remaining_output,
      `SerrePositivity.EInfinity.IntervalCuts.compositeInnerPosition_prefix,
      `SerrePositivity.EInfinity.IntervalCuts.compositeInnerPosition_suffix,
      `SerrePositivity.EInfinity.IntervalCuts.remaining_not_mem_inserted_map,
      `SerrePositivity.EInfinity.IntervalCuts.compositeInnerPosition_remaining_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_pivot_eq_inner,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_remaining_output,
      `SerrePositivity.EInfinity.IntervalCuts.inserted_not_mem_substitute_of_no_slot,
      `SerrePositivity.EInfinity.IntervalCuts.inserted_mem_substitute_iff]

@[noinline] private def e2RequiredBatch12 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.IntervalCuts.compositeInnerPosition_inserted_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_pivot_inserted_output,
      `SerrePositivity.EInfinity.IntervalCuts.inserted_mem_substitute_single_iff,
      `SerrePositivity.EInfinity.IntervalCuts.inserted_mem_substitute_single_tail_iff,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_single_inserted_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_vertex_inserted_output,
      `SerrePositivity.EInfinity.IntervalCuts.edge_slot_list_counts,
      `SerrePositivity.EInfinity.IntervalCuts.two_partition_segments,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_two_inserted_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_nonpivot_inserted_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_inserted_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.outputFamily,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositePosition_outputFamily,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.outputFamily_tupleDegree,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionEdgeCutTerm_outputFamily,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_composition_nested_output_sum,
      `SerrePositivity.EInfinity.IntervalCuts.lineRank_after_pivot_eq_degree,
      `SerrePositivity.EInfinity.IntervalCuts.caesuraRank_pivot_eq_degree,
      `SerrePositivity.EInfinity.IntervalCuts.segmentDegree_single,
      `SerrePositivity.EInfinity.IntervalCuts.segmentDegree_two_zero,
      `SerrePositivity.EInfinity.IntervalCuts.segmentDegree_two_one,
      `SerrePositivity.EInfinity.IntervalCuts.segmentDegree_cast_count,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionExponent_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionSign_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.partition_segmentDegree_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionExponent_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionSign_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionSign_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_append,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_arity_transport,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_arity_transport,
      `SerrePositivity.EInfinity.IntervalCuts.appendIso_tensorVector,
      `SerrePositivity.EInfinity.IntervalCuts.appendIso_tensorVectorAt,
      `SerrePositivity.EInfinity.IntervalCuts.appendIso_inv_tensorVectorAt,
      `SerrePositivity.EInfinity.IntervalCuts.coInsertionBlocks,
      `SerrePositivity.EInfinity.IntervalCuts.tensorCoInsertionAction_on_blocks,
      `SerrePositivity.EInfinity.IntervalCuts.coInsertionBlocks_apply,
      `SerrePositivity.EInfinity.IntervalCuts.coInsertionBlocks_face_apply,
      `SerrePositivity.EInfinity.IntervalCuts.prefixFamily,
      `SerrePositivity.EInfinity.IntervalCuts.suffixFamily,
      `SerrePositivity.EInfinity.IntervalCuts.insertionFamily,
      `SerrePositivity.EInfinity.IntervalCuts.insertionFamily_eq_blocks,
      `SerrePositivity.EInfinity.IntervalCuts.family_eq_blocks,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_prefixFamily,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_family_blocks,
      `SerrePositivity.EInfinity.IntervalCuts.tupleDegree_insertionFamily,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.innerOutputFamily,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.outputFamily_eq_insertion,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.outputFamily_eq_blocks,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.innerOutputFamily_tupleDegree,
      `SerrePositivity.EInfinity.IntervalCuts.tensorVectorAt_family_blocks,
      `SerrePositivity.EInfinity.IntervalCuts.tensorCoInsertionAction_face_apply,
      `SerrePositivity.EInfinity.IntervalCuts.coInsertionBlocks_face_sum_apply,
      `SerrePositivity.EInfinity.IntervalCuts.tensorCoInsertionAction_face_sum_apply,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCutValid,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.output,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.coefficient,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.output_tupleDegree,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.edgeEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.vertexEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.isEmpty_of_nonedge_of_degree_ne_zero,
      `SerrePositivity.EInfinity.IntervalCuts.faceCutSum,
      `SerrePositivity.EInfinity.IntervalCuts.faceCutSum_edge,
      `SerrePositivity.EInfinity.IntervalCuts.faceCutSum_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_basis_vertex_cut_sum,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_basis_edge_cut_sum,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_basis_face_cut_sum,
      `SerrePositivity.EInfinity.IntervalCuts.tensorCoInsertionAction_cochain_basis_sum,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.faceCutEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.outputFamily_eq_faceCut,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.sum_faceCuts,
      `SerrePositivity.EInfinity.IntervalCuts.tensorCoInsertionAction_cochain_basis_sum_at,
      `SerrePositivity.EInfinity.IntervalCuts.coactionComposition_apply,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_apply,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_basis_edge_nonzero_sum,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_edge_cut_sum,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.outputFamily_tupleDegree_all,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.actionCoefficient,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.actionCoefficient_eq,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_edge_nested_sum,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_edge,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_image_of_terms,
      `SerrePositivity.EInfinity.IntervalCuts.substitute_prefix_length_at_non_slot,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_lt,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_lt_iff,
      `SerrePositivity.EInfinity.IntervalCuts.remainingPosition_lt_iff,
      `SerrePositivity.EInfinity.IntervalCuts.mem_activePositions_iff_output_and_le,
      `SerrePositivity.EInfinity.IntervalCuts.activePosition_color_ne_of_nonedge,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_of_ne,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_lt_iff,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_injOn,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_mem_active,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_image_of_degree_zero,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_inversionTerm,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.inversionCount_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.edgeSign_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.actionCoefficient_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionCoefficient_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionEdgeCutTerm_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_ordered_union,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_ordered_images,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_last,
      `SerrePositivity.EInfinity.IntervalCuts.compositeOuterPosition_lt_inner,
      `SerrePositivity.EInfinity.IntervalCuts.insertedPosition_lt_remaining_iff,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.pivotInnerMap,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.pivotInnerMap_lt_iff,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.pivotInnerMap_value,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.pivotInnerMap_at_cut,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remaining_color_ne_of_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.pivotInnerMap_injective,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_pivot_order,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_pivot_injOn,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.pivotInnerMap_mem_active,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_pivot_mem_active,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.activePositions_pivot_union,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_inversionTerm_of_ne,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.pivotInnerMap_inversionTerm,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.inversionCount_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.edgeSign_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionCoefficient_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionEdgeCutTerm_pivot,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_disjoint_union,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_erase_pair,
      `SerrePositivity.EInfinity.IntervalCuts.positionInversionCount_splice_images,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivot_first_length]

@[noinline] private def e2RequiredBatch13 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivot_first_caesura,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivot_first_mem_active,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap_val,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap_value,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap_lt_iff,
      `SerrePositivity.EInfinity.IntervalCuts.remainingPosition_lt_inserted_iff,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remaining_color_ne_of_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_lt_nonpivotInnerMap,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap_lt_remainingPositionMap,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_at_nonpivot_cut,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_nonpivot_injOn,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap_injOn,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap_mem_active,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.remainingPositionMap_nonpivot_mem_active,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivot_active_images_disjoint,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.activePositions_nonpivot_union,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivotInnerMap_inversionTerm,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nonpivot_cross_inversionTerm,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.inversionCount_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionCoefficient_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionEdgeCutTerm_nonpivot,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.compositionCoefficient,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_composition_action_sum,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_edge_eq_iterated,
      `SerrePositivity.EInfinity.IntervalCuts.occurrenceCount_degree_zero,
      `SerrePositivity.EInfinity.IntervalCuts.overlapPartition_card_of_count_one,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_composition_zero,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_vertex_eq,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_basis_vertex_component,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.vertex_not_edge,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.val_eq_none_of_nonedge,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.output_of_nonedge,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.coefficient_of_nonedge,
      `SerrePositivity.EInfinity.IntervalCuts.FaceCut.card_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.insertionFamily_const,
      `SerrePositivity.EInfinity.IntervalCuts.prefixDegree_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.tensorCoInsertionAction_basis_vertex_zero,
      `SerrePositivity.EInfinity.IntervalCuts.tensorCoInsertionAction_basis_vertex_zero_degree,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_apply_of_sums,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_vertex_component,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_vertex_outer_positive,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_vertex_zero_outer,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_vertex_inner_positive,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_vertex_zero,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_vertex_eq_iterated,
      `SerrePositivity.EInfinity.IntervalCuts.complex_basis_linear_ext,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInput_linear_ext,
      `SerrePositivity.EInfinity.IntervalCuts.faceVector_edge_eq,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInput_linear_ext,
      `SerrePositivity.EInfinity.IntervalCuts.coefficient_vertex_linear_ext,
      `SerrePositivity.EInfinity.IntervalCuts.coefficient_edge_linear_ext,
      `SerrePositivity.EInfinity.IntervalCuts.wordPairVertexInput,
      `SerrePositivity.EInfinity.IntervalCuts.wordPairEdgeInput,
      `SerrePositivity.EInfinity.IntervalCuts.coefficient_interval_hom_ext,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_comp_positive,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_operad_comp_positive,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_compositeGenerator_zero,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_composition_zero_all,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_vertex_eq_iterated_all,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullary_eq_none,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullary_occurrenceCount,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullary_slot_nonedge,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullary_pivot_ne_slot,
      `SerrePositivity.EInfinity.IntervalCuts.iteratedCochainAction_basis_edge_nullary_of_count_ne_one,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_edge_nullary_of_count_ne_one,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_edge_nullary_eq_iterated_of_count_ne_one,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_list,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_surjective,
      `SerrePositivity.EInfinity.IntervalCuts.compositeGenerator_nullaryRawWord,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_outerPosition,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_prefix,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_suffix,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_cut_iff,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_cut_preimage,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawCutEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryOuterCutEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryNestedCutEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawCutWord,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryRawWord_outputVertices,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryNestedCutEquiv_outputFamily,
      `SerrePositivity.EInfinity.IntervalCuts.nullaryNestedCutEquiv_remaining_output,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullaryPositionMap,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullaryPositionMap_image,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullaryPositionMap_inversionTerm,
      `SerrePositivity.EInfinity.IntervalCuts.NestedEdgeCut.nullary_edgeSign,
      `SerrePositivity.EInfinity.IntervalCuts.overlapPartition_empty_eq,
      `SerrePositivity.EInfinity.IntervalCuts.compositionOnWords_nullary_eq_generator,
      `SerrePositivity.EInfinity.IntervalCuts.edgeComponent_composition_nullary_action_sum,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_composition_basis_edge_nullary_eq_iterated,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_comp,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_operad_comp,
      `SerrePositivity.EInfinity.IntervalCuts.surjectionCoalgebra,
      `SerrePositivity.EInfinity.IntervalCuts.barrattEcclesCoalgebra,
      `SerrePositivity.EInfinity.IntervalCuts.barrattEcclesCoalgebra_coaction,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainCounit_zero_apply,
      `SerrePositivity.EInfinity.AlexanderWhitney.cochainCounit_generator_zero,
      `SerrePositivity.EInfinity.IntervalCuts.endpointCycle,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_zero_apply,
      `SerrePositivity.EInfinity.IntervalCuts.contraction,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_contraction,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_vertex_eq,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_eq_zero_of_ne_zero,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_endpoint_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.contractionHomotopyComponent,
      `SerrePositivity.EInfinity.IntervalCuts.contractionHomotopyComponent_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.contractionHomotopy,
      `SerrePositivity.EInfinity.IntervalCuts.contractionHomotopyEquiv,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_quasiIso,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_quasiIso,
      `SerrePositivity.EInfinity.IntervalCuts.vertexInputLift_face,
      `SerrePositivity.EInfinity.IntervalCuts.edgeInputLift_face,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMapComponent,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMapComponent_zero,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMapComponent_negOne,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMapComponent_other,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMapComponent_comm,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMap,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMap_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.intervalMap_edge,
      `SerrePositivity.EInfinity.IntervalCuts.interval_hom_ext,
      `SerrePositivity.EInfinity.IntervalCuts.unit_hom_ext,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_intervalMap_apply,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_triangle_value]

@[noinline] private def e2RequiredBatch14 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.IntervalCuts.interval_relative_lift,
      `SerrePositivity.EInfinity.IntervalCuts.boundary,
      `SerrePositivity.EInfinity.IntervalCuts.boundary_contraction,
      `SerrePositivity.EInfinity.IntervalCuts.boundary_cofibration,
      `SerrePositivity.EInfinity.Surjection.zeroAugmentation,
      `SerrePositivity.EInfinity.Surjection.zeroAugmentation_generator,
      `SerrePositivity.EInfinity.Surjection.zeroAugmentation_empty,
      `SerrePositivity.EInfinity.TableReduction.zeroAugmentation_normalizedMap_generator,
      `SerrePositivity.EInfinity.TableReduction.zeroAugmentation_normalizedMap,
      `SerrePositivity.EInfinity.TableReduction.zeroAugmentation_cochainMap_zero,
      `SerrePositivity.EInfinity.IntervalCuts.zeroTensor,
      `SerrePositivity.EInfinity.IntervalCuts.map_zeroTensor,
      `SerrePositivity.EInfinity.IntervalCuts.zeroTensor_unit,
      `SerrePositivity.EInfinity.IntervalCuts.zeroTensor_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.vertexComponent_zero_coefficient,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_zero_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_power_unit,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_power_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.unitPower_isZero_of_ne_zero,
      `SerrePositivity.EInfinity.IntervalCuts.unit_zero_eq_smul,
      `SerrePositivity.EInfinity.IntervalCuts.unitPower_expand_zero,
      `SerrePositivity.EInfinity.IntervalCuts.unit_leftUnitor_right_one,
      `SerrePositivity.EInfinity.IntervalCuts.unitCoaction_zero_one,
      `SerrePositivity.EInfinity.IntervalCuts.barrattEcclesCoaction_zero_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_coaction_zero_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.contraction_coaction,
      `SerrePositivity.EInfinity.IntervalCuts.cochainAction_positive_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.barrattEcclesCoaction_positive_vertex,
      `SerrePositivity.EInfinity.IntervalCuts.unit_zero_linear_ext,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_coaction_zero_one,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_coaction_positive_one,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_coaction_positive_one_at,
      `SerrePositivity.EInfinity.IntervalCuts.endpoint_coaction,
      `SerrePositivity.EInfinity.IntervalCuts.coalgebraInterval,
      `SerrePositivity.EInfinity.BarrattEccles.modelCategory,
      `SerrePositivity.EInfinity.BarrattEccles.modelCategory_weakEquivalences,
      `SerrePositivity.EInfinity.BarrattEccles.modelCategory_fibrations,
      `SerrePositivity.EInfinity.BarrattEccles.modelCategory_cofibrantlyGenerated,
      `SerrePositivity.EInfinity.BarrattEccles.forget_isRightQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.fibration_iff,
      `SerrePositivity.EInfinity.BarrattEccles.weakEquivalence_iff,
      `SerrePositivity.EInfinity.BarrattEccles.isFibrant,
      `SerrePositivity.EInfinity.BarrattEccles.overPullback_isRightQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.overForget_isRightQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.pullbackFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.pullbackFunctor_isRightQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.pullbackFunctor_hasPointwiseRightDerivedFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.fibrationReplacement,
      `SerrePositivity.EInfinity.BarrattEccles.fibrationReplacement_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.fibrationReplacement_surjective,
      `SerrePositivity.EInfinity.BarrattEccles.replacementOver,
      `SerrePositivity.EInfinity.BarrattEccles.replacementInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.replacementInclusion_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.replacementOver_isFibrant,
      `SerrePositivity.EInfinity.BarrattEccles.homotopyPullback,
      `SerrePositivity.EInfinity.BarrattEccles.homotopyPullbackCarrierIso,
      `SerrePositivity.EInfinity.BarrattEccles.homotopyPullbackDerivedIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierPullbackFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.carrierPullbackFunctor_isRightQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.carrierReplacementOver,
      `SerrePositivity.EInfinity.BarrattEccles.carrierReplacementInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.carrierReplacementInclusion_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.carrierReplacementOver_isFibrant,
      `SerrePositivity.EInfinity.BarrattEccles.homotopyPullbackCarrierDerivedIso,
      `SerrePositivity.EInfinity.tensorInsertionAction_coeff,
      `SerrePositivity.EInfinity.tensorInsertionComposition_coeff,
      `SerrePositivity.EInfinity.Operad.restrictAlgebraObj,
      `SerrePositivity.EInfinity.Operad.restrictAlgebraMap,
      `SerrePositivity.EInfinity.Operad.restrictAlgebra,
      `SerrePositivity.EInfinity.powerProduct,
      `SerrePositivity.EInfinity.powerProduct_index,
      `SerrePositivity.EInfinity.powerProduct_one,
      `SerrePositivity.EInfinity.powerProduct_append,
      `SerrePositivity.EInfinity.powerProduct_adjacent,
      `SerrePositivity.EInfinity.powerProduct_permutation,
      `SerrePositivity.EInfinity.powerProduct_insertionCore,
      `SerrePositivity.EInfinity.powerProduct_insertion,
      `SerrePositivity.EInfinity.powerProduct_map,
      `SerrePositivity.EInfinity.commutativeAlgebraOfMonoid,
      `SerrePositivity.EInfinity.commutativeAlgebraMap,
      `SerrePositivity.EInfinity.commutativeAlgebraFunctor,
      `SerrePositivity.EInfinity.moduleCommMonoid,
      `SerrePositivity.EInfinity.moduleCommMonoidMap,
      `SerrePositivity.EInfinity.moduleCommMonoidFunctor,
      `SerrePositivity.EInfinity.discreteCommutativeFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.discreteAlgebraFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.discreteAlgebraFunctor_carrier,
      `SerrePositivity.EInfinity.BarrattEccles.discreteAlgebraFunctor_map,
      `SerrePositivity.EInfinity.BarrattEccles.discreteAlgebraFunctor_action,
      `SerrePositivity.EInfinity.HomologyZero.quotientIso,
      `SerrePositivity.EInfinity.HomologyZero.classMap,
      `SerrePositivity.EInfinity.HomologyZero.classMap_surjective,
      `SerrePositivity.EInfinity.HomologyZero.classMap_eq_zero_iff,
      `SerrePositivity.EInfinity.HomologyZero.unitCycleLinearEquiv,
      `SerrePositivity.EInfinity.HomologyZero.unitClass,
      `SerrePositivity.EInfinity.HomologyZero.unitClass_surjective,
      `SerrePositivity.EInfinity.HomologyZero.unitClass_eq_iff,
      `SerrePositivity.EInfinity.HomologyZero.unitClass_out_map,
      `SerrePositivity.EInfinity.HomologyZero.homotopyClassMap,
      `SerrePositivity.EInfinity.HomologyZero.homotopyClassMap_apply_map,
      `SerrePositivity.EInfinity.HomologyZero.homotopyClassMap_bijective,
      `SerrePositivity.EInfinity.HomologyZero.unitHomLinearEquiv,
      `SerrePositivity.EInfinity.HomologyZero.unit_homotopy_eq,
      `SerrePositivity.EInfinity.HomologyZero.representative,
      `SerrePositivity.EInfinity.HomologyZero.representative_class,
      `SerrePositivity.EInfinity.HomologyZero.representative_homotopy,
      `SerrePositivity.EInfinity.HomologyZero.unitPairing,
      `SerrePositivity.EInfinity.HomologyZero.unitPairingHomotopy,
      `SerrePositivity.EInfinity.HomologyZero.pairingValue,
      `SerrePositivity.EInfinity.HomologyZero.pairingValue_class,
      `SerrePositivity.EInfinity.HomologyZero.pairingValue_add_left,
      `SerrePositivity.EInfinity.HomologyZero.pairingValue_add_right,
      `SerrePositivity.EInfinity.HomologyZero.pairingValue_smul_left,
      `SerrePositivity.EInfinity.HomologyZero.pairingValue_smul_right,
      `SerrePositivity.EInfinity.HomologyZero.pairing,
      `SerrePositivity.EInfinity.HomologyZero.pairing_homotopy,
      `SerrePositivity.EInfinity.HomologyZero.pairing_braiding,
      `SerrePositivity.EInfinity.BarrattEccles.aritySection,
      `SerrePositivity.EInfinity.BarrattEccles.aritySection_augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.homologyOperation,
      `SerrePositivity.EInfinity.BarrattEccles.homologyBinary,
      `SerrePositivity.EInfinity.BarrattEccles.homologyProduct,
      `SerrePositivity.EInfinity.BarrattEccles.homologyOne,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientBinary,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientBinaryHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientPairing_independent,
      `SerrePositivity.EInfinity.BarrattEccles.homologyProduct_eq_pairing]

@[noinline] private def e2RequiredBatch15 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.BarrattEccles.homologyOperation_commutative,
      `SerrePositivity.EInfinity.BarrattEccles.homologyBinary_commutative,
      `SerrePositivity.EInfinity.BarrattEccles.homologyNullary_commutative,
      `SerrePositivity.EInfinity.BarrattEccles.homologyBinary_discrete,
      `SerrePositivity.EInfinity.BarrattEccles.homologyNullary_discrete,
      `SerrePositivity.EInfinity.HomologyZero.binaryInput_braiding,
      `SerrePositivity.EInfinity.BarrattEccles.permutationHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.actionPermutationHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.homologyBinaryCommutativityHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.homologyProduct_comm,
      `SerrePositivity.EInfinity.BarrattEccles.homologyUnaryHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.homologyUnary_class,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientOperation,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientComposite,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientOperation_comp,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientComposite_augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.coefficientOperationHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.homologyCompositionHomotopy,
      `SerrePositivity.EInfinity.HomologyZero.nullaryBinaryInsertion,
      `SerrePositivity.EInfinity.BarrattEccles.homologyBinaryLeftUnitHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.homologyProduct_one_left,
      `SerrePositivity.EInfinity.BarrattEccles.homologyProduct_one_right,
      `SerrePositivity.EInfinity.HomologyZero.ternaryInput,
      `SerrePositivity.EInfinity.HomologyZero.binaryAssociativityLeftInput,
      `SerrePositivity.EInfinity.HomologyZero.binaryAssociativityRightInput,
      `SerrePositivity.EInfinity.BarrattEccles.homologyBinaryAssociativityHomotopy,
      `SerrePositivity.EInfinity.BarrattEccles.homologyProduct_assoc,
      `SerrePositivity.EInfinity.BarrattEccles.homologyCommRing,
      `SerrePositivity.EInfinity.BarrattEccles.homologyCommRing_mul,
      `SerrePositivity.EInfinity.BarrattEccles.homologyCommRing_one,
      `SerrePositivity.EInfinity.BarrattEccles.homologyAlgebra,
      `SerrePositivity.EInfinity.BarrattEccles.homologyAlgebra_algebraMap,
      `SerrePositivity.EInfinity.BarrattEccles.homologyCommAlgebra,
      `SerrePositivity.EInfinity.Operad.AlgebraDiagram.free,
      `SerrePositivity.EInfinity.Operad.AlgebraDiagram.evaluation,
      `SerrePositivity.EInfinity.Operad.AlgebraDiagram.adjunction,
      `SerrePositivity.EInfinity.Operad.AlgebraDiagram.generators,
      `SerrePositivity.EInfinity.Operad.AlgebraDiagram.freeFamily_smallObjectArgument,
      `SerrePositivity.EInfinity.Operad.AlgebraDiagram.generatingCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.Operad.AlgebraDiagram.generatingTrivialCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.generatingCofibrations,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.generatingTrivialCofibrations,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.generatingTrivialCofibrations_component,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.freeCells_acyclic,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.projectiveModelCategory,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.weakEquivalence_iff,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.fibration_iff,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.cofibrantlyGenerated,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.isFibrant,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.forget,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.objectwiseQuasiIsos,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.projectiveModelCategory_weakEquivalences,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.forget_inverts,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.localizedForget,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.localizedForgetComparison,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.localizedForget_isRightDerivedFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.forget_hasPointwiseRightDerivedFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.productFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.productFunctor_isRightQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.product_map_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.productFunctor_hasPointwiseRightDerivedFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.productDerivedIso,
      `SerrePositivity.EInfinity.BarrattEccles.productCarrierIso,
      `SerrePositivity.EInfinity.OppositeFactorization.arrowUnop,
      `SerrePositivity.EInfinity.OppositeFactorization.opposite,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameFactorization,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrame,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameComparison,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameComparison_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrame_cofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrame_map_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.cotensor,
      `SerrePositivity.EInfinity.BarrattEccles.cotensorHomEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.cotensorSimplexIso,
      `SerrePositivity.EInfinity.FrameRealizationLifting.map_monomorphism,
      `SerrePositivity.EInfinity.FrameRealizationLifting.map_anodyne,
      `SerrePositivity.EInfinity.BarrattEccles.cotensor_map_fibration,
      `SerrePositivity.EInfinity.BarrattEccles.cotensor_map_trivialFibration,
      `SerrePositivity.EInfinity.BarrattEccles.carrierComplex_hasLimitsOfSize,
      `SerrePositivity.EInfinity.BarrattEccles.carrierCotensor,
      `SerrePositivity.EInfinity.BarrattEccles.cotensorCarrierIso,
      `SerrePositivity.EInfinity.BarrattEccles.cotensorCarrierIso_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.doubleOpWeights,
      `SerrePositivity.EInfinity.BarrattEccles.weightedCotensor,
      `SerrePositivity.EInfinity.BarrattEccles.weightedCotensorHomEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrameDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.carrierWeightedCotensor,
      `SerrePositivity.EInfinity.BarrattEccles.weightedCotensorCarrierIso,
      `SerrePositivity.EInfinity.HomotopyWeight.free,
      `SerrePositivity.EInfinity.HomotopyWeight.evaluation,
      `SerrePositivity.EInfinity.HomotopyWeight.adjunction,
      `SerrePositivity.EInfinity.HomotopyWeight.boundaries,
      `SerrePositivity.EInfinity.HomotopyWeight.boundaries_smallObjectArgument,
      `SerrePositivity.EInfinity.HomotopyWeight.boundaries_rlp,
      `SerrePositivity.EInfinity.HomotopyWeight.point,
      `SerrePositivity.EInfinity.HomotopyWeight.pointFactorization,
      `SerrePositivity.EInfinity.HomotopyWeight.weight,
      `SerrePositivity.EInfinity.HomotopyWeight.comparison,
      `SerrePositivity.EInfinity.HomotopyWeight.weight_cofibrant,
      `SerrePositivity.EInfinity.HomotopyWeight.comparison_rlp,
      `SerrePositivity.EInfinity.HomotopyWeight.reindex_cofibration,
      `SerrePositivity.EInfinity.HomotopyWeight.realization_map_cofibration,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpace_map_boundary_rlp,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpace_map_fibration,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpace_kanComplex,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpace_map_isIso_of_boundary_rlp,
      `SerrePositivity.EInfinity.HomotopyWeight.frameCone,
      `SerrePositivity.EInfinity.HomotopyWeight.frameCone_target_boundary_rlp,
      `SerrePositivity.EInfinity.HomotopyWeight.frameCone_kanComplex,
      `SerrePositivity.EInfinity.HomotopyWeight.frameCone_source_boundary_rlp,
      `SerrePositivity.EInfinity.HomotopyWeight.frameCone_target_weakEquivalence_isIso,
      `SerrePositivity.EInfinity.HomotopyWeight.frameCone_source_trivialCofibration_isIso,
      `SerrePositivity.EInfinity.HomotopyWeight.frameCone_source_weakEquivalence_isIso,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorRealization,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorRealizationAdjunction,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorRealization_map_mono,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorRealization_map_anodyne,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorFrame,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorFrame_reedyCofibrant,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorFrameHomIso,
      `SerrePositivity.EInfinity.HomotopyWeight.unitTensorWeightIso,
      `SerrePositivity.EInfinity.HomotopyWeight.zeroTensorWeightIso,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorFrameZeroIso,
      `SerrePositivity.EInfinity.HomotopyWeight.frameConePiZeroLocalizationEquiv]

@[noinline] private def e2RequiredBatch16 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.HomotopyWeight.frameConePiZeroLocalizationEquiv_mk,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorRealization_homEquiv_frame_naturality,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorFrameHomIso_source_naturality,
      `SerrePositivity.EInfinity.HomotopyWeight.frameConePiZeroLocalizationEquiv_source,
      `SerrePositivity.EInfinity.HomotopyWeight.realization_map_frame_weakEquivalence,
      `SerrePositivity.EInfinity.FrameRealizationLifting.map_boundary_rlp_weakEquivalence,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseRealization,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseFrameHom,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseRealizationAdjunction,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseRealization_map_cofibration,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseRealization_isCofibrant,
      `SerrePositivity.EInfinity.HomotopyWeight.liftedZeroPointIso,
      `SerrePositivity.EInfinity.HomotopyWeight.realizationPointIso,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseFrameComparison,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseFrameComparison_weakEquivalence,
      `SerrePositivity.EInfinity.HomotopyWeight.realizationPointIso_naturality,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseFrameComparison_app,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseFrameComparison_naturality,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorRealization,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseWeightedHom,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorAdjunction,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrame,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrameHomIso,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrameZeroIso,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorRealization_map_mono,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrame_reedyCofibrant,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorRealization_map_anodyne,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv_mk,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseWeightedHomPiZeroEquiv_target,
      `SerrePositivity.EInfinity.HomotopyWeight.comparison_mono_rlp,
      `SerrePositivity.EInfinity.HomotopyWeight.weight_kanComplex,
      `SerrePositivity.EInfinity.HomotopyWeight.valueSection,
      `SerrePositivity.EInfinity.HomotopyWeight.valueSection_comparison,
      `SerrePositivity.EInfinity.HomotopyWeight.valueContraction,
      `SerrePositivity.EInfinity.BarrattEccles.weightedCotensor_map_fibration,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitWeight,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitOpFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor_obj,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitCarrierIso,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.strictConeWeightedFamily,
      `SerrePositivity.EInfinity.BarrattEccles.coneToFramedLimit,
      `SerrePositivity.EInfinity.BarrattEccles.weightedCotensorHomEquiv_precomp,
      `SerrePositivity.EInfinity.BarrattEccles.coneToFramedLimit_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.limitComparison,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameDiagramFamily,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitHomEquiv_map,
      `SerrePositivity.EInfinity.BarrattEccles.limitComparison_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.limitComparisonNatTrans,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSpace,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitWeight_cofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor_map_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramReplacement,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramComparison,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramReplacement_isCofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramComparison_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramComparison_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramReplacement_map_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramHomEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramLocalizedIso,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.trivialFibration_app,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.fibration_app,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameFamily,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrame,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceHom,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameHomIso,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameZeroIso,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrame_reedyCofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceHom_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameComparison,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameComparison_zero,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameComparison_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameZeroIso_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourcePiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourcePiZeroEquiv_mk,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourcePiZeroEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceClass,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourcePiZeroEquiv_class,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.mappingCofibrantFactorization,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.mappingSpace,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.mappingSpace_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.mappingSpacePiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameMappingComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceMappingComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSpace_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSpace_map_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSpace_map_piZero_bijective,
      `SerrePositivity.EInfinity.FrameHom.map_isIso_of_fibrant,
      `SerrePositivity.EInfinity.FrameHom.map_isIso_of_pointwise_cofibrant,
      `SerrePositivity.EInfinity.FrameHom.StandardFrame.reedyCofibrant,
      `SerrePositivity.EInfinity.FrameHom.StandardFrame.homotopicallyConstant,
      `SerrePositivity.EInfinity.FrameHom.StandardFrame.homIso,
      `SerrePositivity.EInfinity.FrameHom.weakEquivalence_of_localized_precomposition_fibrant,
      `SerrePositivity.EInfinity.FrameHom.target_boundary_rlp,
      `SerrePositivity.EInfinity.FrameHom.target_trivialFibration_isIso,
      `SerrePositivity.EInfinity.FrameHom.target_weakEquivalence_isIso,
      `SerrePositivity.EInfinity.FrameHom.source_boundary_rlp,
      `SerrePositivity.EInfinity.FrameHom.source_trivialCofibration_isIso,
      `SerrePositivity.EInfinity.FrameHom.source_weakEquivalence_isIso,
      `SerrePositivity.EInfinity.FrameHom.comparison_left_isIso,
      `SerrePositivity.EInfinity.FrameHom.comparison_right_isIso,
      `SerrePositivity.EInfinity.FrameHom.frameChoiceIso,
      `SerrePositivity.EInfinity.HomotopyWeight.map_isIso_of_pointwiseKan,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpace_map_isIso_of_pointwiseKan,
      `SerrePositivity.EInfinity.HomotopyWeight.kanReplacement_map_isIso,
      `SerrePositivity.EInfinity.HomotopyWeight.kanDiagram,
      `SerrePositivity.EInfinity.HomotopyWeight.kanDiagramUnit,
      `SerrePositivity.EInfinity.HomotopyWeight.kanDiagramMap,
      `SerrePositivity.EInfinity.HomotopyWeight.kanDiagram_kanComplex,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpace_kanDiagramUnit_isIso,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpace_kanDiagramMap_isIso,
      `SerrePositivity.EInfinity.HomotopyWeight.coneComparisonArrow,
      `SerrePositivity.EInfinity.HomotopyWeight.coneComparisonArrow_isIso,
      `SerrePositivity.EInfinity.HomotopyWeight.kanConeComparisonIso,
      `SerrePositivity.EInfinity.HomotopyWeight.kanConeComparisonIso_fac,
      `SerrePositivity.EInfinity.HomotopyWeight.coneComparisonArrow_naturality,
      `SerrePositivity.EInfinity.HomotopyWeight.kanConeComparisonIso_naturality,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.mixedFunctor,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightHomFunctor,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.leftComparison,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightComparison,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightHomIso]

@[noinline] private def e2RequiredBatch17 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.FrameHom.MixedFrame.flipIso,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.fibrantOp_of_cofibrant,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.leftComparison_isIso,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightComparison_isIso,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.leftDiagram,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.mixedDiagram,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightDiagram,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.leftDiagramComparison,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightDiagramComparison,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.leftDiagram_kanComplex,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightDiagram_kanComplex,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.leftDiagramComparison_isIso,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightDiagramComparison_isIso,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.mixedConeComparisonIso,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpaceReindexAuxIso,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpaceReindexIso,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialFrameFamily,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialFrameAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialFrameAugmentation_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialFrame_fibrant,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialFrame_cofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparison_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialHomDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialHomFamily,
      `SerrePositivity.EInfinity.BarrattEccles.rightFrameHomDiagramFamily,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialHomDiagramIso,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialHomComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialConeComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialConeIso,
      `SerrePositivity.EInfinity.BarrattEccles.sourceRightConeComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.sourceRightConeComparisonNatIso,
      `SerrePositivity.EInfinity.BarrattEccles.sourceRightConeComparisonNatIso_app,
      `SerrePositivity.EInfinity.BarrattEccles.constantProbeLocalizedIso,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConePiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConePiZeroEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitHomPiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitDerivedHomEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitHomPiZeroEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitDerivedHomEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor_obj,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeComparisonNatTrans,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor_map_quasiIso,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.mixedSourceMap,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightSourceMap,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.leftDiagramComparison_source,
      `SerrePositivity.EInfinity.FrameHom.MixedFrame.rightDiagramComparison_source,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeBifunctor,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeBifunctor_obj,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSourceMap,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeSourceMap_app,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialHomSourceMap,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialHomDiagramIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialConeIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceBifunctor,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceBifunctor_obj,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceMap,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceMap_app,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeLocalizedIso,
      `SerrePositivity.EInfinity.HomotopyWeight.frameConePiZeroLocalizationEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.sourceRightConeComparisonIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.sourceRightConeComparisonIso_source_inv,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitHomPiZeroEquiv_source,
      `SerrePositivity.EInfinity.FrameHom.realizationHomEquiv_app,
      `SerrePositivity.EInfinity.FrameHom.realizationHomEquiv_source,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseRealization_homEquiv_source,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorAdjunction_source,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrameHomIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramFrameHomIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourcePiZeroEquiv_source,
      `SerrePositivity.EInfinity.BarrattEccles.constantProbeLocalizedNatIso,
      `SerrePositivity.EInfinity.BarrattEccles.constantProbeLocalizedNatIso_app,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConePiZeroEquiv_source,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitDerivedHomEquiv_source,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.leftHom,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.rightHom,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.restrict,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.descendHomIso,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.descendHomIso_hom_app,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.adjunctionOfHomIso,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.descendAdjunction,
      `SerrePositivity.EInfinity.FrameHom.LocalizedAdjunction.descendAdjunction_homEquiv_app,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagram_inverts,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimit_inverts,
      `SerrePositivity.EInfinity.BarrattEccles.localizedConstantDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.localizedFramedLimit,
      `SerrePositivity.EInfinity.BarrattEccles.localizedConstantDiagramComparison,
      `SerrePositivity.EInfinity.BarrattEccles.localizedFramedLimitComparison,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitRawLeftHom,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitRawRightHom,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitRawHomIso,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitRestrictedHomIso,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitAdjunction,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitAdjunction_homEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitAdjunction_homEquiv_comparison,
      `SerrePositivity.EInfinity.HomotopyWeight.conePoint,
      `SerrePositivity.EInfinity.HomotopyWeight.coneClass,
      `SerrePositivity.EInfinity.HomotopyWeight.conePoint_map,
      `SerrePositivity.EInfinity.HomotopyWeight.coneClass_map,
      `SerrePositivity.EInfinity.HomotopyWeight.tensorFrameHomIso_point,
      `SerrePositivity.EInfinity.HomotopyWeight.frameConePiZeroLocalizationEquiv_class,
      `SerrePositivity.EInfinity.HomotopyWeight.realizationAugmentation_homEquiv,
      `SerrePositivity.EInfinity.HomotopyWeight.pointwiseTensorFrameHomIso_point,
      `SerrePositivity.EInfinity.HomotopyWeight.kanDiagramUnit_naturality,
      `SerrePositivity.EInfinity.HomotopyWeight.coneComparisonArrow_class,
      `SerrePositivity.EInfinity.HomotopyWeight.kanConeComparisonIso_class,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramSourceClass_eq_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.constantDiagramHomEquiv_comparison_app,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConeClass,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitHomPiZeroEquiv_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.strictSimplicialConeFamily,
      `SerrePositivity.EInfinity.BarrattEccles.strictSimplicialConeFamily_app,
      `SerrePositivity.EInfinity.BarrattEccles.strictConeFamilies_mixed,
      `SerrePositivity.EInfinity.BarrattEccles.sourceRightConeComparisonIso_strictClass,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpaceReindexIso_homEquiv,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpaceReindexIso_point,
      `SerrePositivity.EInfinity.HomotopyWeight.coneSpaceReindexIso_class,
      `SerrePositivity.EInfinity.BarrattEccles.rightSimplicialConeIso_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.sourceRightConeComparisonIso_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitConePiZeroEquiv_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitDerivedHomEquiv_cone,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitAdjunction_homEquiv_cone,
      `SerrePositivity.EInfinity.FrameHom.AdjointRightDerived.transformationEquiv,
      `SerrePositivity.EInfinity.FrameHom.AdjointRightDerived.transformationEquiv_app,
      `SerrePositivity.EInfinity.FrameHom.AdjointRightDerived.comparison]

@[noinline] private def e2RequiredBatch18 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.FrameHom.AdjointRightDerived.transformationEquiv_eq,
      `SerrePositivity.EInfinity.FrameHom.AdjointRightDerived.isLeftKanExtension,
      `SerrePositivity.EInfinity.FrameHom.AdjointRightDerived.comparison_app,
      `SerrePositivity.EInfinity.FrameHom.AdjointRightDerived.isRightDerivedFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitDerivedComparison,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitDerivedComparison_eq,
      `SerrePositivity.EInfinity.BarrattEccles.localizedFramedLimit_isRightDerivedFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.limitFunctor_hasRightDerivedFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitDerivedIso,
      `SerrePositivity.EInfinity.BarrattEccles.forgetOp_isLeftQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrame,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrame_cofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrameAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrameAugmentation_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrameDiagram_obj,
      `SerrePositivity.EInfinity.BarrattEccles.carrierProbeFactorization,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbeFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbe,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbeComparison,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbe_cofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbeComparison_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrameDiagramFamily,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeSpace,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeSpace_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitHomPiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitMapClass,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitHomPiZeroEquiv_mapClass,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.free,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.evaluation,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.adjunction,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.generators,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.freeFamily_smallObjectArgument,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.generatingCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.generatingTrivialCofibrations_smallObjectArgument,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.freeCells_acyclic,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.projectiveModelCategory,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.weakEquivalence_iff,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.fibration_iff,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.cofibrantlyGenerated,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.isFibrant,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramReplacement,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramComparison,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramReplacement_isCofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramComparison_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramComparison_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramReplacement_map_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramHomEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramLocalizedIso,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.trivialFibration_app,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.fibration_app,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameFamily,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrame,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceHom,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameHomIso,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameZeroIso,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrame_reedyCofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceHom_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameComparison,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameComparison_zero,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameComparison_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameZeroIso_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv_mk,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceClass,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv_class,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceClass_eq_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramHomEquiv_comparison_app,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.carrierModelCategory_weakEquivalences,
      `SerrePositivity.EInfinity.BarrattEccles.Diagram.forget_isRightQuillen,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialFrameFamily,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialFrameAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialFrameAugmentation_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialFrame_fibrant,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialFrame_cofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialFrame_homotopicallyConstant,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialHomDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialHomFamily,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightFrameHomDiagramFamily,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialHomDiagramIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialHomComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialConeComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialConeIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierSourceRightConeComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierSourceRightConeComparisonNatIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierSourceRightConeComparisonNatIso_app,
      `SerrePositivity.EInfinity.BarrattEccles.carrierConstantProbeLocalizedIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConePiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConePiZeroEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitDerivedHomEquiv,
      `SerrePositivity.EInfinity.HomotopyWeight.realizationHomEquiv_app,
      `SerrePositivity.EInfinity.HomotopyWeight.realizationHomEquiv_lan_source,
      `SerrePositivity.EInfinity.HomotopyWeight.realizationMap_eq_lan,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitOpFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitCarrierIso_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitCarrierNatIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitHomPiZeroEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitDerivedHomEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceBifunctor,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceBifunctor_obj,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceMap,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourceMap_app,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramFrameHomIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.constantDiagramSourcePiZeroEquiv_source,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeBifunctor,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeBifunctor_obj,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeSourceMap,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeSourceMap_app,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialHomSourceMap,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialHomDiagramIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialConeIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitProbeLocalizedIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierConstantProbeLocalizedNatIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierConstantProbeLocalizedNatIso_app,
      `SerrePositivity.EInfinity.BarrattEccles.carrierSourceRightConeComparisonIso_source,
      `SerrePositivity.EInfinity.BarrattEccles.carrierSourceRightConeComparisonIso_source_inv,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConePiZeroEquiv_source,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitHomPiZeroEquiv_source,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitDerivedHomEquiv_source,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitDerivedHomEquiv_both,
      `SerrePositivity.EInfinity.BarrattEccles.carrierStrictConeWeightedFamily,
      `SerrePositivity.EInfinity.BarrattEccles.carrierConeToFramedLimit,
      `SerrePositivity.EInfinity.BarrattEccles.carrierStrictSimplicialConeFamily]

@[noinline] private def e2RequiredBatch19 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.BarrattEccles.carrierStrictConeFamilies_mixed,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeClass,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConeClass_eq_mapClass,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitHomPiZeroEquiv_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.carrierSourceRightConeComparisonIso_strictClass,
      `SerrePositivity.EInfinity.BarrattEccles.carrierRightSimplicialConeIso_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.carrierSourceRightConeComparisonIso_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.weightedCotensorCarrierHomEquiv_app,
      `SerrePositivity.EInfinity.BarrattEccles.carrierConeToFramedLimit_forget,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitConePiZeroEquiv_coneClass,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitDerivedHomEquiv_cone,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitDerivedHomEquiv_forgetCone,
      `SerrePositivity.EInfinity.ComplexLimits.rightFrameFactorization,
      `SerrePositivity.EInfinity.ComplexLimits.rightFrameFamily,
      `SerrePositivity.EInfinity.ComplexLimits.rightFrame_cofibrant,
      `SerrePositivity.EInfinity.ComplexLimits.weightedCotensorHomEquiv,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitFunctor,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitWeight_cofibrant,
      `SerrePositivity.EInfinity.ComplexLimits.coneToFramedLimit,
      `SerrePositivity.EInfinity.ComplexLimits.limitComparisonNatTrans,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitFunctor_map_quasiIso,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitConeSpace_kanComplex,
      `SerrePositivity.EInfinity.ComplexLimits.sourceRightConeComparisonIso,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitDerivedHomEquiv,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitDerivedHomEquiv_source,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitDerivedHomEquiv_target,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitAdjunction,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitDerivedHomEquiv_cone,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitAdjunction_homEquiv_cone,
      `SerrePositivity.EInfinity.ComplexLimits.localizedFramedLimit_isRightDerivedFunctor,
      `SerrePositivity.EInfinity.ComplexLimits.limitFunctor_hasRightDerivedFunctor,
      `SerrePositivity.EInfinity.ComplexLimits.framedLimitDerivedIso,
      `SerrePositivity.EInfinity.FrameHom.RepresentedLocalization.comparisonIso,
      `SerrePositivity.EInfinity.FrameHom.RepresentedLocalization.comparisonIso_hom_app,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitRestrictedHomIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitComparisonIso_cone,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitComparisonIso_forgetCone,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitComparisonIso_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.carrierFramedLimitComparisonNatIso,
      `SerrePositivity.EInfinity.BarrattEccles.framedLimitCarrierDerivedIso,
      `SerrePositivity.EInfinity.BarrattEccles.complexRelativeCategory,
      `SerrePositivity.EInfinity.BarrattEccles.cAlgForgetRelative,
      `SerrePositivity.EInfinity.BarrattEccles.complexLocalizationNerve,
      `SerrePositivity.EInfinity.BarrattEccles.complexLocalizationNerve_quasicategory,
      `SerrePositivity.EInfinity.BarrattEccles.cAlgForgetLocalization,
      `SerrePositivity.EInfinity.BarrattEccles.cAlgForgetLocalization_vertex,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.powerMap,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.powerMap_id,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.powerMap_comp,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.face_naturality,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.degeneracy_naturality,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.augmentation_naturality,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.oppositeMap_naturality,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.oppositeMap,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.presentationMap,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.resolutionMap,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.resolutionMap_app,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.resolutionMap_id,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.resolutionMap_comp,
      `SerrePositivity.EInfinity.FrameHom.ComonadResolution.resolutionMap_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomEdgeComposition,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsComposition,
      `SerrePositivity.EInfinity.SimplicialLocalization.LocalizationComponents,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsCategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsAugmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionAugmentation_object,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomConstant,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomAugmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomAugmentation_identity,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomAugmentation_composition,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomAugmentation_edge,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomPiZeroToHom,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomPiZeroToHom_mk,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomMap_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomMap_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationEnrichedMap_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationEnrichedMap_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationEnrichedMap_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationEnrichedMap_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomKanUnit_naturality,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveMap_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveMap_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionObject_zero,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationArrowZero,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationArrowClass,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomAugmentation_arrow,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsAugmentation_arrow,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKObject,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKPiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKPiZeroEquiv_class,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraKanDKPiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraKanDKPiZeroEquiv_class,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.liftedWeakEquivalences,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.down,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.up,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.down_up,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.up_down,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.equivalence,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.homEquiv,
      `SerrePositivity.EInfinity.FrameHom.ULiftRelativeLocalization.homEquiv_map,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationZeroHom_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsLift_augmentation_zero,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsAugmentation_comp_lift,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsEquivalence,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsQ_isLocalization,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomPiZeroEquiv,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomPiZeroEquiv_arrow,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsQ_inverts,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsLift,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsLift_fac,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsQ_comp_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsLift_comp_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.strictLocalizationCounit_comp_componentsLift,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomKanUnitPiZeroEquiv,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationHomPiZeroEquiv,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationHomPiZeroEquiv_arrow,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionHom_delta_zero,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionHom_delta_one,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionGeneratorObject,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionGeneratorObject_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionObject_generator,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionHom,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionHom_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionHom_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionHom_zero_arrow,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionWordEdge]

@[noinline] private def e2RequiredBatch20 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.SimplicialLocalization.localizationResolutionWordClass,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationArrowClass_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationArrowClass_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComponentsQ,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationZeroHom,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationZeroHom_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationZeroHom_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.zeroLevelComponentsFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.zeroLevelComponentsFunctor_arrow,
      `SerrePositivity.EInfinity.SimplicialLocalization.zeroLevelComponentsFunctor_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpecialHammock,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockFunctor_left_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockFunctor_right_quasiIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockValue_zero,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockNerveMap,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.inclusion,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow,
      `SerrePositivity.EInfinity.FrameHom.LeftTrivialThreeArrow,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.specialInclusion,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.leftInclusion,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.left_weakEquivalence,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.right_weakEquivalence,
      `SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.liftUnit,
      `SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.liftCounit,
      `SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.of_unit,
      `SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.of_counit,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.arrow,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.arrowMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.arrowMap_id,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.arrowMap_comp,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.intermediate,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.first,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.last,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.intermediateMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.fac,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.map_first,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.map_last,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.first_trivialCofibration,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.right,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.inl,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.inr,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.inr_trivialCofibration,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.rightMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.inl_rightMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.inr_rightMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.rightMap_id,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.rightMap_comp,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.obj,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.map,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.functor,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.unit,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.LeftReplacement.inclusion_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.arrow,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.arrowMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.arrowMap_id,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.arrowMap_comp,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.intermediate,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.first,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.last,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.intermediateMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.fac,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.map_first,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.map_last,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.last_trivialFibration,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.left,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.fst,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.snd,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.fst_trivialFibration,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.leftMap,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.leftMap_fst,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.leftMap_snd,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.leftMap_id,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.leftMap_comp,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.obj,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.map,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.functor,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.counit,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement.inclusion_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.inclusion,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.inclusion_fac,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.inclusion_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.inclusion_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.algebraWeakThreeArrow,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpecialThreeArrowInclusionNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpecialThreeArrowInclusionNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceWeakThreeArrowNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceWeakThreeArrowNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceWeakThreeArrowNerveMap_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceWeakThreeArrowComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceWeakThreeArrowComparisonIso_fac,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.smallFunctor,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.diagram,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.commaDown,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.commaUp,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.commaDown_commaUp,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.commaUp_commaDown,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.commaEquivalence,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.equivalence,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.recoveryNerveMap,
      `SerrePositivity.EInfinity.FrameHom.SmallCommaGrothendieck.recoveryNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallSpanRecoveryNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallSpanRecoveryNerveMap_middle,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallSpanRecoveryNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSmallSpanGrothendieckNerveMap_fac,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockNerveMap_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpanGrothendieckNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceIndexAugmentation_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockComparisonIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockComparisonIso_fac,
      `SerrePositivity.EInfinity.FrameHom.Thomason.fiberNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.toComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.fromComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.toComma_fromComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.fromComma_toComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.equivalence,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.toComma_naturality,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.map_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallDiagram,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallToComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallFromComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallToComma_smallFromComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallFromComma_smallToComma,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallEquivalence,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallElementsMap,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallToComma_naturality,
      `SerrePositivity.EInfinity.FrameHom.SmallNerve.functor]

@[noinline] private def e2RequiredBatch21 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.FrameHom.SmallNerve.naturality,
      `SerrePositivity.EInfinity.FrameHom.SmallNerve.map_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.CosimplicialHomElements.smallCommaMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallRightSpanInitial,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallRightSpanInitial_isInitial,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallResolutionRightDiagram_map_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionFiberNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceResolutionRightLeg,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceResolutionFiberEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceResolutionFiberNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceResolutionFiberNerveMap_hom,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceResolutionFiberNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceResolutionGrothendieckNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceResolutionGrothendieckNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSmallSpanGrothendieckNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSmallSpanGrothendieckNerveMap_hom,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSmallSpanGrothendieckNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.Thomason.commaDiagram,
      `SerrePositivity.EInfinity.FrameHom.Thomason.transport,
      `SerrePositivity.EInfinity.FrameHom.Thomason.transport_naturality,
      `SerrePositivity.EInfinity.FrameHom.Thomason.transportComparison,
      `SerrePositivity.EInfinity.FrameHom.Thomason.fiberIntoComma,
      `SerrePositivity.EInfinity.FrameHom.Thomason.fiberIntoComma_transport,
      `SerrePositivity.EInfinity.FrameHom.Thomason.transportUnit,
      `SerrePositivity.EInfinity.FrameHom.Thomason.transport_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.Thomason.commaTotalForget,
      `SerrePositivity.EInfinity.FrameHom.Thomason.commaTotalTransport,
      `SerrePositivity.EInfinity.FrameHom.Thomason.selfLiftIso,
      `SerrePositivity.EInfinity.FrameHom.Thomason.commaSimplex_forget,
      `SerrePositivity.EInfinity.FrameHom.Thomason.commaMap_forget,
      `SerrePositivity.EInfinity.FrameHom.Thomason.commaMap_forget_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.Thomason.map_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.Thomason.map_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionThomason_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpanThomason_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.Thomason.nerveDiagram,
      `SerrePositivity.EInfinity.FrameHom.Thomason.values,
      `SerrePositivity.EInfinity.FrameHom.Thomason.simplex,
      `SerrePositivity.EInfinity.FrameHom.Thomason.simplex_operator,
      `SerrePositivity.EInfinity.FrameHom.Thomason.map,
      `SerrePositivity.EInfinity.FrameHom.Thomason.fiberNerveMap,
      `SerrePositivity.EInfinity.FrameHom.Thomason.valueInclusion_map,
      `SerrePositivity.EInfinity.FrameHom.Thomason.simplex_base,
      `SerrePositivity.EInfinity.FrameHom.Thomason.map_vertex,
      `SerrePositivity.EInfinity.FrameHom.Thomason.nerveComparison,
      `SerrePositivity.EInfinity.FrameHom.Thomason.simplex_naturality,
      `SerrePositivity.EInfinity.FrameHom.Thomason.map_naturality,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.values,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.chain,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.chain_map,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.lift,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.initial,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.lift_reconstruct,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.retraction,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.contraction,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.projection,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.inclusion,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.inclusion_projection,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.projection_inclusion,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.projection_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.projectionRows,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.barProjection,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.barProjection_app,
      `SerrePositivity.EInfinity.FrameHom.CommaNerve.barProjection_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallResolutionRightDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallSpanRightDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionBarComparison,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionBarComparison_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionThomasonSquare,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.values,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.first_label,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.projection,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.inclusion,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.inclusion_projection,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.retraction,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.projection_inclusion,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.contraction,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.projection_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.labels,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.projectionRows,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.inclusionRows,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.inclusionRows_projectionRows,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.labelsDiagonalIso,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.augmentation,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.augmentation_app,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.valueInclusion,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.valueInclusion_augmentation,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.augmentation_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.ConstantBar.valueInclusion_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.BarRows.valueInclusion,
      `SerrePositivity.EInfinity.FrameHom.BarRows.constantInclusion_naturality,
      `SerrePositivity.EInfinity.FrameHom.BarRows.valueInclusion_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomBarInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomBarInclusion_app,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomBarInclusion_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFibrantRightLeg,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceBarInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceBarInclusion_app,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceBarInclusion_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceIndexBarMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceIndexBarMap_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.BarRows.row,
      `SerrePositivity.EInfinity.FrameHom.BarRows.inclusion,
      `SerrePositivity.EInfinity.FrameHom.BarRows.cofan,
      `SerrePositivity.EInfinity.FrameHom.BarRows.desc,
      `SerrePositivity.EInfinity.FrameHom.BarRows.isColimit,
      `SerrePositivity.EInfinity.FrameHom.BarRows.rowMap,
      `SerrePositivity.EInfinity.FrameHom.BarRows.inclusion_rowMap,
      `SerrePositivity.EInfinity.FrameHom.BarRows.rowMap_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.BarRows.diagonalFlipIso,
      `SerrePositivity.EInfinity.FrameHom.BarRows.diagonalFlipIso_naturality,
      `SerrePositivity.EInfinity.FrameHom.BarRows.map_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.BarRows.fromInitial,
      `SerrePositivity.EInfinity.FrameHom.BarRows.fromInitial_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomFromIdentity,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomFromIdentity_app,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomFromIdentity_bar_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFixedRightGrothendieckComparison_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFixedRightGrothendieckComparison_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.FrameHom.CommaPreLeft.projection_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.CommaPreLeft.comparison_isLeftCofinal,
      `SerrePositivity.EInfinity.FrameHom.CommaPreLeft.comparison_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.CommaPreLeft.projection,
      `SerrePositivity.EInfinity.FrameHom.CommaPreLeft.canonicalSection,
      `SerrePositivity.EInfinity.FrameHom.CommaPreLeft.canonicalSection_projection,
      `SerrePositivity.EInfinity.FrameHom.CommaPreLeft.contraction,
      `SerrePositivity.EInfinity.FrameHom.fixedRightGrothendieckComparison_toComma,
      `SerrePositivity.EInfinity.FrameHom.fixedRightGrothendieckComparison_localized_isIso]

@[noinline] private def e2RequiredBatch22 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.FrameHom.NerveQuillenA.nerveMap_isLeftCofinal_of_weaklyContractible_comma,
      `SerrePositivity.EInfinity.FrameHom.NerveQuillenA.comma_isWeaklyContractible,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionFixedRightComparison,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionFixedRightComparison_isLeftCofinal,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionFixedRightComparison_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionFixedRightComparison_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallRightSpanForget,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFixedRightDiagramComparison,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFixedRightDiagramComparison_isLeftCofinal,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFixedRightDiagramComparison_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFixedRightGrothendieckComparison,
      `SerrePositivity.EInfinity.FrameHom.leftAnodyne_anodyne,
      `SerrePositivity.EInfinity.FrameHom.leftCofinal_image_isIso,
      `SerrePositivity.EInfinity.FrameHom.leftCofinal_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.costructuredArrowProjection_rightFibration,
      `SerrePositivity.EInfinity.FrameHom.costructuredArrowPre_isPullback,
      `SerrePositivity.EInfinity.FrameHom.costructuredArrowPre_isLeftCofinal,
      `SerrePositivity.EInfinity.FrameHom.costructuredArrowDiagramPre,
      `SerrePositivity.EInfinity.FrameHom.costructuredArrowDiagramPre_isLeftCofinal,
      `SerrePositivity.EInfinity.FrameHom.fixedRightGrothendieckComparison,
      `SerrePositivity.EInfinity.FrameHom.smallResolutionLeftForget,
      `SerrePositivity.EInfinity.FrameHom.smallResolutionOverFunctor_leftForget,
      `SerrePositivity.EInfinity.FrameHom.resolutionFixedRightComparison,
      `SerrePositivity.EInfinity.FrameHom.resolutionFixedRightComparison_isLeftCofinal,
      `SerrePositivity.EInfinity.FrameHom.resolutionFixedRightComparison_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.FrameHom.resolutionFixedRightComparison_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.rightFibration_pullback_isLeftCofinal,
      `SerrePositivity.EInfinity.FrameHom.rightFibration_isPullback_isLeftCofinal,
      `SerrePositivity.EInfinity.BarrattEccles.algebraRightSpanBase,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpanRightDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpanFromGrothendieck,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpanGrothendieckEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpanGrothendieckFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpanGrothendieckFunctor_fac,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.mappingRightHomDiagram_map_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpanGrothendieckNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpanFromGrothendieckNerveMap,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpanGrothendieckNerveMap_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraSpanFromGrothendieckNerveMap_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpecialHammockNerveMap_localized_isIso_iff,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.leftSliceForget,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightSliceForget,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.toComma,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.fromComma,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.toComma_fromComma,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.commaEquivalence,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightDiagram,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.toGrothendieck,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.fromGrothendieck,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.toGrothendieck_fromGrothendieck,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.grothendieckEquivalence,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.frameGrothendieckFunctor,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.frameGrothendieckFunctor_fac,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.frameGrothendieckFunctor_base,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.frameGrothendieckFunctor_middle,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightSliceInitial,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightSliceInitial_isInitial,
      `SerrePositivity.EInfinity.FrameHom.CommaGrothendieck.diagram,
      `SerrePositivity.EInfinity.FrameHom.CommaGrothendieck.toComma,
      `SerrePositivity.EInfinity.FrameHom.CommaGrothendieck.toComma_faithful,
      `SerrePositivity.EInfinity.FrameHom.CommaGrothendieck.toComma_full,
      `SerrePositivity.EInfinity.FrameHom.CommaGrothendieck.toComma_essSurj,
      `SerrePositivity.EInfinity.FrameHom.CommaGrothendieck.fromComma,
      `SerrePositivity.EInfinity.FrameHom.CommaGrothendieck.equivalence,
      `SerrePositivity.EInfinity.FrameHom.costructuredArrowDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallResolutionOverFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallResolutionOverFunctor_isLeftCofinal,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSmallResolutionOverFunctor_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents,
      `SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.homComponents_inverts,
      `SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.FrameHom.AnodyneWeakDetection.isWeaklyContractible,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.smallFunctor,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.smallFunctor_up,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.comparison,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.comparison_faithful,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.comparison_full,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.comparison_essSurj,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.equivalence,
      `SerrePositivity.EInfinity.FrameHom.NerveAsSmall.up_down,
      `SerrePositivity.EInfinity.FrameHom.NerveAsSmall.down_up,
      `SerrePositivity.EInfinity.FrameHom.NerveAsSmall.iso,
      `SerrePositivity.EInfinity.FrameHom.NerveAsSmall.terminal_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.NerveQuillenA.nerveMap_isLeftCofinal,
      `SerrePositivity.EInfinity.FrameHom.smallResolutionOverFunctor,
      `SerrePositivity.EInfinity.FrameHom.smallResolutionOverFunctor_isLeftCofinal,
      `SerrePositivity.EInfinity.FrameHom.smallResolutionOverFunctor_isWeakHomotopyEquivalence,
      `SerrePositivity.EInfinity.FrameHom.AsSmallComma.terminal_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.algebraTrivialFibrationOver,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionOverFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.mappingResolutionCommaTerminal_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.overFunctor,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.toComma,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.toComma_faithful,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.toComma_full,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.toComma_essSurj,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.commaEquivalence,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.projection_mono_rlp,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.projection_image_isIso,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.elementsTerminal_image_isIso,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.evaluationPullback,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.pointSimplex_unique,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.inclusion_injective,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.simplexEquiv,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.simplexEquiv_naturality,
      `SerrePositivity.EInfinity.FrameHom.NerveEquivalenceImage.imageIso,
      `SerrePositivity.EInfinity.FrameHom.TrivialFibrationOver,
      `SerrePositivity.EInfinity.FrameHom.resolutionOverFunctor,
      `SerrePositivity.EInfinity.FrameHom.resolutionOverFunctor_forget,
      `SerrePositivity.EInfinity.FrameHom.resolutionOverComma_image_isIso,
      `SerrePositivity.EInfinity.FrameHom.resolutionCommaTerminal_image_isIso,
      `SerrePositivity.EInfinity.FrameHom.FrameLift.commaTerminal_image_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceIndexAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceIndexAugmentation_localized_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceIndexAugmentation_zero,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceSpanComparison_vertex,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.liftedAugmentation,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.liftedAugmentation_zero,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality,
      `SerrePositivity.EInfinity.FrameHom.chosenResolutionSpanValue_augmentation,
      `SerrePositivity.EInfinity.FrameHom.NerveTerminalImage.contraction,
      `SerrePositivity.EInfinity.FrameHom.NerveTerminalImage.terminalImageIso,
      `SerrePositivity.EInfinity.FrameHom.NerveULiftHom.up_down,
      `SerrePositivity.EInfinity.FrameHom.NerveULiftHom.down_up,
      `SerrePositivity.EInfinity.FrameHom.NerveULiftHom.iso,
      `SerrePositivity.EInfinity.FrameHom.NerveULiftHom.naturality]

@[noinline] private def e2RequiredBatch23 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.FrameHom.SimplexTerminalAugmentation.parameter,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalAugmentation.simplex,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalAugmentation.simplex_operator,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalAugmentation.augmentation,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalAugmentation.augmentation_zero,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalAugmentation.naturality,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.augmentation_localized_isIso,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.augmentation_image_isIso,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.augmentationImageIso,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.functor,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.oppositeIso,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.augmentation,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalParameter.tail_comp,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalParameter.vertex,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalParameter.monotone,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalParameter.parameter,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalParameter.parameter_apply,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalParameter.parameter_last,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalParameter.reindex,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.standardIsTerminal,
      `SerrePositivity.EInfinity.FrameHom.SimplexTerminalNerve.standardAugmentation_isIso,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.Object,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.Hom,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.hom_ext,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.objectCategory,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.leftProjection,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightProjection,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.leftAugmentation,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.rightAugmentation,
      `SerrePositivity.EInfinity.FrameHom.ArrowSpan.middleTransformation,
      `SerrePositivity.EInfinity.FrameHom.frameElementSpan,
      `SerrePositivity.EInfinity.FrameHom.frameElementSpanMap,
      `SerrePositivity.EInfinity.FrameHom.frameElementSpanFunctor,
      `SerrePositivity.EInfinity.FrameHom.frameSpanSourceComparison,
      `SerrePositivity.EInfinity.FrameHom.frameSpanTargetComparison,
      `SerrePositivity.EInfinity.FrameHom.frameElementSpanNerveMap,
      `SerrePositivity.EInfinity.FrameHom.chosenResolutionSpanNerveMap,
      `SerrePositivity.EInfinity.FrameHom.chosenResolutionSpanValue_zero,
      `SerrePositivity.EInfinity.FrameHom.chosenResolutionSpanValue_naturality,
      `SerrePositivity.EInfinity.FrameHom.resolutionAugmentation_trivialFibration,
      `SerrePositivity.EInfinity.FrameHom.resolutionSpecialSpanFunctor,
      `SerrePositivity.EInfinity.FrameHom.fibrantTargetComparison_trivialCofibration,
      `SerrePositivity.EInfinity.FrameHom.chosenResolutionSpanFunctor,
      `SerrePositivity.EInfinity.FrameHom.SpecialHammock,
      `SerrePositivity.EInfinity.FrameHom.SpecialHammock.left_weakEquivalence,
      `SerrePositivity.EInfinity.FrameHom.SpecialHammock.right_weakEquivalence,
      `SerrePositivity.EInfinity.FrameHom.SpecialHammock.value,
      `SerrePositivity.EInfinity.FrameHom.SpecialHammock.value_eq,
      `SerrePositivity.EInfinity.FrameHom.SpecialHammock.valueFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationEnrichedMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.coefficientMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.coefficientMap_naturality,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.coefficientMap_identity,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.coefficientMap_composition,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.coefficientNatTrans,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionMap_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationEnrichedMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionMap_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionMap_object,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveMap_vertex,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.map,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.map_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.map_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.map_identity,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.map_composition,
      `SerrePositivity.EInfinity.SimplicialLocalization.FixedObjectHom.functor,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHom,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationIdentity,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationComposition,
      `SerrePositivity.EInfinity.SimplicialLocalization.LocalizationObjects,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationEnrichedCategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.LocalizationCategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationSimplicialCategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationCategory_sHom,
      `SerrePositivity.EInfinity.SimplicialLocalization.KanLocalizationObjects,
      `SerrePositivity.EInfinity.SimplicialLocalization.KanLocalizationCategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationCategory_sHom,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationHom_kanComplex,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationHomKanUnit_anodyne,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationUnit,
      `SerrePositivity.EInfinity.SimplicialLocalization.kanLocalizationUnitFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerve,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerve_quasicategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizationNerveVertexEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.CAlgSimplicialCategory,
      `SerrePositivity.EInfinity.BarrattEccles.CAlg_R,
      `SerrePositivity.EInfinity.BarrattEccles.cAlg_R_quasicategory,
      `SerrePositivity.EInfinity.BarrattEccles.cAlg_sHom,
      `SerrePositivity.EInfinity.BarrattEccles.cAlg_sHom_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.cAlgVertexEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.cAlgVertex,
      `SerrePositivity.EInfinity.BarrattEccles.discreteCAlgVertex,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeCounit_obj_bijective,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeComonadAugmentation_obj_bijective,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionAugmentation_obj_bijective,
      `SerrePositivity.EInfinity.SimplicialLocalization.strictLocalizationMap_obj_bijective,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionAugmentation_obj_bijective,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionObjectEquiv,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionObject,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionObject_naturality,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeComonadPower_eq,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolution_obj,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolution_face,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolution_degeneracy,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionAugmentationNatTrans,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionAugmentationNatTrans_app,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolution,
      `SerrePositivity.EInfinity.SimplicialLocalization.localizedFreeResolutionAugmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.strictLocalizationMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.strictLocalizationMap_fac,
      `SerrePositivity.EInfinity.SimplicialLocalization.strictLocalizationMap_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.strictLocalizationMap_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.strictLocalizationFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraFreeResolution,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraFreeResolutionAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraLocalizedFreeResolution,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraLocalizedFreeResolutionAugmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeFunctor,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeCounit,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeDiagonal]

@[noinline] private def e2RequiredBatch24 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeComonad,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeMap,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeCounit,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeDiagonal,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeMap_id,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeRelativeMap_comp,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeCounit_naturality,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeDiagonal_naturality,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeDiagonal_left_counit,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeDiagonal_right_counit,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeDiagonal_coassoc,
      `SerrePositivity.EInfinity.SimplicialLocalization.freePower,
      `SerrePositivity.EInfinity.SimplicialLocalization.freePowerAugmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionLevel,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionAugmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionOuterFace,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionOuterDegeneracy,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionOuterFace_augmentation,
      `SerrePositivity.EInfinity.SimplicialLocalization.freeResolutionOuterDegeneracy_face,
      `SerrePositivity.EInfinity.SimplicialLocalization.RelativeCategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.relativeCategoryCategory,
      `SerrePositivity.EInfinity.SimplicialLocalization.relativeFunctor_ext,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraHoEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraInclusionLocalizedIso,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraInclusion_isLocalizedEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraInclusion_isLocalization,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraMappingSpacePiZeroEquiv_class,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraMappingSpace,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraMappingSpace_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraMappingSpacePiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraRelativeCategory,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraRelativeCategory_weakEquivalences_iff,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKInclusionRelative,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKReplacement,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKReplacement_comp_inclusion,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKReplacementRelative,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKForget,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraDKForgetRelative,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraFreeLevel,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraFreeAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraReplacement,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraReplacement_comp_inclusion,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraReplacementRelative,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraReplacementComparison,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraReplacementComparison_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraRestrictedComparison,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraRestrictedComparison_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.CofibrantAlgebra,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraWeakEquivalences,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraWeakEquivalences_isMultiplicative,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebra_isCofibrant,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebra_isFibrant,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraWeakEquivalences_iff,
      `SerrePositivity.EInfinity.BarrattEccles.cofibrantAlgebraInclusionRelative,
      `SerrePositivity.EInfinity.BarrattEccles.discreteCofibrantAlgebraFunctor,
      `SerrePositivity.EInfinity.BarrattEccles.discreteCofibrantAlgebraComparison,
      `SerrePositivity.EInfinity.BarrattEccles.discreteCofibrantAlgebraComparison_app,
      `SerrePositivity.EInfinity.BarrattEccles.discreteCofibrantAlgebraComparison_weakEquivalence,
      `SerrePositivity.EInfinity.BarrattEccles.discreteAlgebraDKFunctor,
      `SerrePositivity.EInfinity.FrameHom.RelativeLocalization.equivalence,
      `SerrePositivity.EInfinity.FrameHom.RelativeLocalization.equivalence_functor,
      `SerrePositivity.EInfinity.FrameHom.RelativeLocalization.equivalence_inverse,
      `SerrePositivity.EInfinity.FrameHom.overFunctor_left_isIso,
      `SerrePositivity.EInfinity.FrameHom.overFunctor_right_isIso,
      `SerrePositivity.EInfinity.FrameHom.overFunctorChoiceIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization,
      `SerrePositivity.EInfinity.BarrattEccles.mappingFibrantFactorization,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpace,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpace_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpacePiZeroEquiv,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpacePiZeroEquiv_source,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpacePiZeroEquiv_target,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpaceClass,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpacePiZeroEquiv_class,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpace_map_target_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpace_map_source_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.mappingSpace_map_both_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.sourceFrameHom,
      `SerrePositivity.EInfinity.BarrattEccles.sourceFrameHom_kanComplex,
      `SerrePositivity.EInfinity.BarrattEccles.sourceFrameHomComparison,
      `SerrePositivity.EInfinity.BarrattEccles.sourceFrameHomComparison_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.sourceFrameHomComparisonIso,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.two,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.twoCut,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.twoCut_two,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.two_twoCut,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.twoEquiv,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.two_start_one,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.two_segment_zero,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.two_segment_one,
      `SerrePositivity.EInfinity.Surjection.CompositeRecovery.input_degrees_unique,
      `SerrePositivity.EInfinity.Surjection.OverlapPartition.collapse_segments,
      `SerrePositivity.EInfinity.TableReduction.fuseBoundary_fst_dropLast,
      `SerrePositivity.EInfinity.TableReduction.reduceRows_row_bounds,
      `SerrePositivity.EInfinity.Surjection.substitute_horizontal_no_slot,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_complete,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_none_between,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_count_take,
      `SerrePositivity.EInfinity.Surjection.occurrenceAt_count_take_succ,
      `SerrePositivity.EInfinity.TableReduction.fuseBoundary_in_context,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.horizontal_vertical_join,
      `SerrePositivity.EInfinity.Surjection.TableCompositionData.vertical_horizontal_join,
      `SerrePositivity.EInfinity.TableReduction.ReductionInterval.weightedVertices_vertex,
      `SerrePositivity.EInfinity.TableReduction.reductionRemoved_first_eq_nil,
      `SerrePositivity.EInfinity.TableReduction.rowFusion_in_context]

@[noinline] private def e2RequiredBatch25 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Direction.endpointsEq,
      `SerrePositivity.EInfinity.Hammock.IdentityColumn,
      `SerrePositivity.EInfinity.Hammock.IdentityOutside,
      `SerrePositivity.EInfinity.Hammock.Word.Hom.no_image_of_cut_eq,
      `SerrePositivity.EInfinity.Hammock.WordAction.identityOutside_obj,
      `SerrePositivity.EInfinity.Hammock.identityFiber_vertex_of_le,
      `SerrePositivity.EInfinity.Hammock.identityFiber_vertex,
      `SerrePositivity.EInfinity.Hammock.identityFiber_embeddingVertex,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.vertex,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.source_eq,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.target_eq,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.arrow,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.arrow_mem,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.obj,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.vertex_eq,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.arrow_heq,
      `SerrePositivity.EInfinity.Hammock.IdentityPreimage.obj_image,
      `SerrePositivity.EInfinity.Hammock.WordAction.obj_range_iff,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_map_range_iff_identityOutside,
      `SerrePositivity.EInfinity.Hammock.Word.subword,
      `SerrePositivity.EInfinity.Hammock.Word.subwordInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.subwordInclusion_injective,
      `SerrePositivity.EInfinity.Hammock.Word.subwordInclusion_range,
      `SerrePositivity.EInfinity.Hammock.Word.columnImage,
      `SerrePositivity.EInfinity.Hammock.Word.coe_columnImage,
      `SerrePositivity.EInfinity.Hammock.Word.intersection,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionInclusion_injective,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionInclusion_range,
      `SerrePositivity.EInfinity.Hammock.identityOutside_intersection,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_intersection_range,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram,
      `SerrePositivity.EInfinity.Hammock.imageHomOfLe_isIso,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.intersectionComparison,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.intersectionComparison_isIso,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.intersectionComparison_fac,
      `SerrePositivity.EInfinity.Hammock.graphDiagram_proper,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockIdentityOutside,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockIdentityPreimage,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockIdentityPreimage_image,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTransition_obj_range_iff,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphMap_range_iff_identityOutside,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphDiagram_proper,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphIntersection_range,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphIntersectionComparison,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphIntersectionComparison_isIso,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphIntersectionComparison_fac,
      `SerrePositivity.EInfinity.Hammock.IdentityColumn.mk,
      `SerrePositivity.EInfinity.Hammock.IdentityColumn.vertex_eq,
      `SerrePositivity.EInfinity.Hammock.IdentityColumn.arrow_eq,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.mk,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.map_mono,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.intersection_range]

@[noinline] private def e2RequiredBatch26 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Word.erase,
      `SerrePositivity.EInfinity.Hammock.Word.eraseInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.eraseInclusion_injective,
      `SerrePositivity.EInfinity.Hammock.Word.erase_length,
      `SerrePositivity.EInfinity.Hammock.Word.erase_length_lt,
      `SerrePositivity.EInfinity.Hammock.Word.eraseInclusion_range,
      `SerrePositivity.EInfinity.Hammock.Word.eraseInclusion_missing_iff,
      `SerrePositivity.EInfinity.Hammock.identityOutside_erase_iff,
      `SerrePositivity.EInfinity.Hammock.Word.mergeTarget,
      `SerrePositivity.EInfinity.Hammock.Word.mergeMap,
      `SerrePositivity.EInfinity.Hammock.Word.mergeMap_surjective,
      `SerrePositivity.EInfinity.Hammock.Word.mergeMap_left,
      `SerrePositivity.EInfinity.Hammock.Word.mergeMap_right,
      `SerrePositivity.EInfinity.Hammock.Word.mergeMap_fiber,
      `SerrePositivity.EInfinity.Hammock.exists_eraseSimplex,
      `SerrePositivity.EInfinity.Hammock.eraseSimplex,
      `SerrePositivity.EInfinity.Hammock.eraseSimplex_fac,
      `SerrePositivity.EInfinity.Hammock.eraseSimplex_unique,
      `SerrePositivity.EInfinity.Hammock.RawHammock,
      `SerrePositivity.EInfinity.Hammock.RawHammock.map,
      `SerrePositivity.EInfinity.Hammock.RawHammock.value,
      `SerrePositivity.EInfinity.Hammock.RawHammock.value_map,
      `SerrePositivity.EInfinity.Hammock.RawHammock.value_transition,
      `SerrePositivity.EInfinity.Hammock.RawHammock.IsReduced,
      `SerrePositivity.EInfinity.Hammock.Reduction,
      `SerrePositivity.EInfinity.Hammock.Reduction.length_lt,
      `SerrePositivity.EInfinity.Hammock.Reduction.value_eq,
      `SerrePositivity.EInfinity.Hammock.Reduction.chain_value_eq,
      `SerrePositivity.EInfinity.Hammock.no_reduction_of_reduced,
      `SerrePositivity.EInfinity.Hammock.exists_reduction_of_not_reduced,
      `SerrePositivity.EInfinity.Hammock.reduced_iff_no_reduction,
      `SerrePositivity.EInfinity.Hammock.exists_reduced_representative,
      `SerrePositivity.EInfinity.Hammock.exists_reduced_same_value,
      `SerrePositivity.EInfinity.Hammock.identityColumn_map,
      `SerrePositivity.EInfinity.Hammock.eraseSimplex_map,
      `SerrePositivity.EInfinity.Hammock.Reduction.map,
      `SerrePositivity.EInfinity.Hammock.Reduction.chain_map,
      `SerrePositivity.EInfinity.Hammock.RawHammock.simplicialSet,
      `SerrePositivity.EInfinity.Hammock.RawHammock.augmentation,
      `SerrePositivity.EInfinity.Hammock.RawHammock.augmentation_app,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRaw,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawMap,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawValue,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawIsReduced,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawReduction,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawReduction_length_lt,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawReduction_value_eq,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawReduction_map,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRaw_existsReducedRepresentative,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRaw_existsReducedSameValue,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRaw_reduced_iff_no_reduction,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawSimplicialSet,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawAugmentation_app,
      `SerrePositivity.EInfinity.Hammock.Reduction.merge,
      `SerrePositivity.EInfinity.Hammock.Reduction.erase]

@[noinline] private def e2RequiredBatch27 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.identityColumn_obj_image_iff,
      `SerrePositivity.EInfinity.Hammock.Word.eqToHom_apply,
      `SerrePositivity.EInfinity.Hammock.Word.embedding_eq_of_range,
      `SerrePositivity.EInfinity.Hammock.Word.erase_composite_range,
      `SerrePositivity.EInfinity.Hammock.raw_eq_of_embeddings,
      `SerrePositivity.EInfinity.Hammock.eraseSimplex_identityColumn,
      `SerrePositivity.EInfinity.Hammock.doubleErase_image,
      `SerrePositivity.EInfinity.Hammock.erase_erase_join,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEraseSimplex,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEraseSimplex_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEraseRaw,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEraseRaw_reduction,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockEraseErase_join]

@[noinline] private def e2RequiredBatch28 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Word.target_eq_of_surjective,
      `SerrePositivity.EInfinity.Hammock.raw_eq_of_surjections,
      `SerrePositivity.EInfinity.Hammock.Word.direction_eq_of_images,
      `SerrePositivity.EInfinity.Hammock.Word.merge_left_remaining_color,
      `SerrePositivity.EInfinity.Hammock.Word.merge_right_remaining_color,
      `SerrePositivity.EInfinity.Hammock.Word.merge_predAbove_comp,
      `SerrePositivity.EInfinity.Hammock.merge_merge_join_ordered,
      `SerrePositivity.EInfinity.Hammock.merge_merge_join_of_lt,
      `SerrePositivity.EInfinity.Hammock.merge_merge_join,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockMergeRaw,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockMergeRaw_reduction,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockMergeMerge_join]

@[noinline] private def e2RequiredBatch29 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Word.puncture,
      `SerrePositivity.EInfinity.Hammock.Word.punctureInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.punctureInclusion_injective,
      `SerrePositivity.EInfinity.Hammock.Word.punctureInclusion_range,
      `SerrePositivity.EInfinity.Hammock.identityOutside_of_complement,
      `SerrePositivity.EInfinity.Hammock.erase_raw_eq_of_embedding,
      `SerrePositivity.EInfinity.Hammock.exists_eraseEmbedding,
      `SerrePositivity.EInfinity.Hammock.erase_reduction_of_embedding,
      `SerrePositivity.EInfinity.Hammock.punctureSimplex,
      `SerrePositivity.EInfinity.Hammock.punctureSimplex_fac,
      `SerrePositivity.EInfinity.Hammock.punctureSimplex_raw_eq,
      `SerrePositivity.EInfinity.Hammock.merge_erase_eq_of_cancel,
      `SerrePositivity.EInfinity.Hammock.merge_erase_overlap_eq,
      `SerrePositivity.EInfinity.Hammock.Word.descendSurjection,
      `SerrePositivity.EInfinity.Hammock.Word.descendSurjection_fac,
      `SerrePositivity.EInfinity.Hammock.merge_erase_join_of_square,
      `SerrePositivity.EInfinity.Hammock.merge_erase_join,
      `SerrePositivity.EInfinity.Hammock.reduction_local_join,
      `SerrePositivity.EInfinity.Hammock.reduction_church_rosser,
      `SerrePositivity.EInfinity.Hammock.chain_eq_of_reduced,
      `SerrePositivity.EInfinity.Hammock.reduced_representative_unique,
      `SerrePositivity.EInfinity.Hammock.normalForm,
      `SerrePositivity.EInfinity.Hammock.normalForm_chain,
      `SerrePositivity.EInfinity.Hammock.normalForm_reduced,
      `SerrePositivity.EInfinity.Hammock.normalForm_eq_of_chain,
      `SerrePositivity.EInfinity.Hammock.normalForm_eq_of_reduction,
      `SerrePositivity.EInfinity.Hammock.normalForm_eq_self,
      `SerrePositivity.EInfinity.Hammock.normalForm_idempotent,
      `SerrePositivity.EInfinity.Hammock.normalForm_value,
      `SerrePositivity.EInfinity.Hammock.normalForm_eq_iff_join,
      `SerrePositivity.EInfinity.Hammock.normalForm_map_normalForm,
      `SerrePositivity.EInfinity.Hammock.reducedSimplicialSet,
      `SerrePositivity.EInfinity.Hammock.normalization,
      `SerrePositivity.EInfinity.Hammock.normalization_app,
      `SerrePositivity.EInfinity.Hammock.reducedAugmentation,
      `SerrePositivity.EInfinity.Hammock.normalization_augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockMergeErase_join,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawReduction_local_join,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawReduction_church_rosser,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockReducedRepresentative_unique,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalForm,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalForm_chain,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalForm_reduced,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalForm_eq_self,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalForm_value,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalForm_map,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockReducedSimplicialSet,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalization,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockReducedAugmentation,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalization_augmentation]

@[noinline] private def e2RequiredBatch30 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Word.factorEmbedding,
      `SerrePositivity.EInfinity.Hammock.Word.adjacent_color_of_image_eq,
      `SerrePositivity.EInfinity.Hammock.Word.factorMerge,
      `SerrePositivity.EInfinity.Hammock.normalForm_transition_bijective,
      `SerrePositivity.EInfinity.Hammock.normalForm_transition,
      `SerrePositivity.EInfinity.Hammock.graphNormalization,
      `SerrePositivity.EInfinity.Hammock.graphNormalization_naturality,
      `SerrePositivity.EInfinity.Hammock.graphNormalization_augmentation,
      `SerrePositivity.EInfinity.Hammock.colimitNormalization,
      `SerrePositivity.EInfinity.Hammock.graphInclusion_colimitNormalization,
      `SerrePositivity.EInfinity.Hammock.colimitNormalization_augmentation,
      `SerrePositivity.EInfinity.Hammock.augmentation_colimitNormalization,
      `SerrePositivity.EInfinity.Hammock.rawAugmentation_colimitNormalization,
      `SerrePositivity.EInfinity.Hammock.reducedColimitIso,
      `SerrePositivity.EInfinity.Hammock.reducedColimitIso_hom_fac,
      `SerrePositivity.EInfinity.Hammock.reducedColimitIso_inv,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockNormalForm_transition,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphNormalization,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphNormalization_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphNormalization_augmentation,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockColimitNormalization,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockGraphInclusion_colimitNormalization,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockReducedColimitIso,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockReducedColimitIso_hom_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockReducedColimitIso_inv,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockRawAugmentation_colimitNormalization]

@[noinline] private def e2RequiredBatch31 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Word.lengthProperty,
      `SerrePositivity.EInfinity.Hammock.Word.LengthBounded,
      `SerrePositivity.EInfinity.Hammock.Word.lengthInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.lengthBoundInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.lengthBoundInclusion_comp,
      `SerrePositivity.EInfinity.Hammock.lengthStage,
      `SerrePositivity.EInfinity.Hammock.lengthStageInclusion,
      `SerrePositivity.EInfinity.Hammock.lengthStageInclusion_naturality,
      `SerrePositivity.EInfinity.Hammock.lengthStageTransition,
      `SerrePositivity.EInfinity.Hammock.lengthStageInclusion_transition,
      `SerrePositivity.EInfinity.Hammock.lengthStageTransition_refl,
      `SerrePositivity.EInfinity.Hammock.lengthStageTransition_comp,
      `SerrePositivity.EInfinity.Hammock.lengthDiagram,
      `SerrePositivity.EInfinity.Hammock.lengthStageToColimit,
      `SerrePositivity.EInfinity.Hammock.lengthStageInclusion_toColimit,
      `SerrePositivity.EInfinity.Hammock.lengthStageToColimit_transition,
      `SerrePositivity.EInfinity.Hammock.lengthCocone,
      `SerrePositivity.EInfinity.Hammock.lengthCocone_component,
      `SerrePositivity.EInfinity.Hammock.lengthReconstructedCocone,
      `SerrePositivity.EInfinity.Hammock.lengthCocone_isColimit,
      `SerrePositivity.EInfinity.Hammock.lengthColimitIso,
      `SerrePositivity.EInfinity.Hammock.lengthColimitIso_fac,
      `SerrePositivity.EInfinity.Hammock.lengthStageMap,
      `SerrePositivity.EInfinity.Hammock.lengthStageInclusion_map,
      `SerrePositivity.EInfinity.Hammock.lengthStageMap_transition,
      `SerrePositivity.EInfinity.Hammock.lengthDiagramMap,
      `SerrePositivity.EInfinity.Hammock.lengthStageToColimit_map,
      `SerrePositivity.EInfinity.Hammock.lengthColimitIso_naturality,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthStage,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthStageInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthTransition,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthStageToColimit,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthStageInclusion_toColimit,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthColimitIso,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthColimitIso_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthColimitIso_word_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthReducedIso,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthReducedIso_word_fac]

@[noinline] private def e2RequiredBatch32 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Direction.other,
      `SerrePositivity.EInfinity.Hammock.Direction.ne_other,
      `SerrePositivity.EInfinity.Hammock.Direction.eq_other_of_ne,
      `SerrePositivity.EInfinity.Hammock.Direction.alternatingSequence,
      `SerrePositivity.EInfinity.Hammock.Word.IsAlternating,
      `SerrePositivity.EInfinity.Hammock.Word.alternating,
      `SerrePositivity.EInfinity.Hammock.Word.alternating_isAlternating,
      `SerrePositivity.EInfinity.Hammock.Word.IsAlternating.map_injective,
      `SerrePositivity.EInfinity.Hammock.Word.IsAlternating.length_le,
      `SerrePositivity.EInfinity.Hammock.Word.alternating_direction_eq,
      `SerrePositivity.EInfinity.Hammock.Word.exists_alternating,
      `SerrePositivity.EInfinity.Hammock.Word.alternating_cases,
      `SerrePositivity.EInfinity.Hammock.Word.alternating_ne,
      `SerrePositivity.EInfinity.Hammock.Word.IsAlternating.target_eq_of_length_le,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionLeft,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionRight,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionLeft_fac,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionRight_fac,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionLeft_injective,
      `SerrePositivity.EInfinity.Hammock.Word.intersectionRight_injective,
      `SerrePositivity.EInfinity.Hammock.Word.intersection_length_le_left,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.map_app_injective,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.overlap_lift,
      `SerrePositivity.EInfinity.Hammock.ProperDiagram.overlap_lengthStage,
      `SerrePositivity.EInfinity.Hammock.lengthBoundary,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation,
      `SerrePositivity.EInfinity.Hammock.lengthBoundary_mem_iff,
      `SerrePositivity.EInfinity.Hammock.boundaryPresentation,
      `SerrePositivity.EInfinity.Hammock.lengthBoundaryStageValue,
      `SerrePositivity.EInfinity.Hammock.lengthBoundaryStageValue_eq,
      `SerrePositivity.EInfinity.Hammock.lengthBoundaryToStage,
      `SerrePositivity.EInfinity.Hammock.lengthBoundary_square,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthBoundary,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthBoundaryToStage,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthBoundaryToStage_app,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthBoundary_square,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockAlternatingGraphMap_mono,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation.mk,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation.source,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation.bound,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation.arrow,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation.injective,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation.simplex,
      `SerrePositivity.EInfinity.Hammock.BoundaryPresentation.image]

@[noinline] private def e2RequiredBatch33 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.Word.merge_cone_ordered,
      `SerrePositivity.EInfinity.Hammock.Word.merge_cone_of_lt,
      `SerrePositivity.EInfinity.Hammock.Word.merge_cone,
      `SerrePositivity.EInfinity.Hammock.Word.topStageProperty,
      `SerrePositivity.EInfinity.Hammock.Word.TopStage,
      `SerrePositivity.EInfinity.Hammock.Word.topStageInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.not_injective_of_not_top,
      `SerrePositivity.EInfinity.Hammock.Word.topMergeObject,
      `SerrePositivity.EInfinity.Hammock.Word.topMergeArrow,
      `SerrePositivity.EInfinity.Hammock.Word.topMergeArrow_zigzag,
      `SerrePositivity.EInfinity.Hammock.Word.exists_adjacent_of_not_alternating,
      `SerrePositivity.EInfinity.Hammock.Word.topStage_comma_connected,
      `SerrePositivity.EInfinity.Hammock.Word.topStageFinal,
      `SerrePositivity.EInfinity.Hammock.topStageDiagram,
      `SerrePositivity.EInfinity.Hammock.topStageColimitIso,
      `SerrePositivity.EInfinity.Hammock.topStageColimitIso_fac,
      `SerrePositivity.EInfinity.Hammock.Word.imageWord,
      `SerrePositivity.EInfinity.Hammock.Word.imageInclusion,
      `SerrePositivity.EInfinity.Hammock.Word.imageInclusion_injective,
      `SerrePositivity.EInfinity.Hammock.Word.imageInclusion_range,
      `SerrePositivity.EInfinity.Hammock.Word.toImage,
      `SerrePositivity.EInfinity.Hammock.Word.toImage_fac,
      `SerrePositivity.EInfinity.Hammock.Word.toImage_surjective,
      `SerrePositivity.EInfinity.Hammock.Word.imageWord_length_le,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTopStageDiagram,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTopStageColimitIso,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTopStageColimitIso_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockTopStageColimitIso_toColimit_fac]

@[noinline] private def e2RequiredBatch34 : Array Lean.Name :=
  #[`SerrePositivity.EInfinity.Hammock.lengthBoundaryLift,
      `SerrePositivity.EInfinity.Hammock.lengthBoundaryLift_ι,
      `SerrePositivity.EInfinity.Hammock.lengthBoundaryLift_toStage,
      `SerrePositivity.EInfinity.Hammock.Word.MaximalAlternating,
      `SerrePositivity.EInfinity.Hammock.Word.maximalAlternating,
      `SerrePositivity.EInfinity.Hammock.Word.maximalAlternating_bijective,
      `SerrePositivity.EInfinity.Hammock.Word.maximalAlternatingEquiv,
      `SerrePositivity.EInfinity.Hammock.Word.maximalAlternating_finite,
      `SerrePositivity.EInfinity.Hammock.StageAttachmentData,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentComponent,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentComponent_short,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentComponent_top,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentComponent_naturality,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentCocone,
      `SerrePositivity.EInfinity.Hammock.topStageColimitIso_inv_fac,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentDesc,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentDesc_fac,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentDesc_lower,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentDesc_upper,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentDesc_unique,
      `SerrePositivity.EInfinity.Hammock.stageBoundarySum,
      `SerrePositivity.EInfinity.Hammock.stageTopSum,
      `SerrePositivity.EInfinity.Hammock.stageBoundarySumInclusion,
      `SerrePositivity.EInfinity.Hammock.stageTopInclusion,
      `SerrePositivity.EInfinity.Hammock.stageBoundarySumInclusion_fac,
      `SerrePositivity.EInfinity.Hammock.stageTopInclusion_fac,
      `SerrePositivity.EInfinity.Hammock.stageBoundaryAttach,
      `SerrePositivity.EInfinity.Hammock.stageBoundaryAttach_fac,
      `SerrePositivity.EInfinity.Hammock.lengthStagePushout_condition,
      `SerrePositivity.EInfinity.Hammock.lengthStagePushoutCocone,
      `SerrePositivity.EInfinity.Hammock.stageAttachmentDataOfPushoutCocone,
      `SerrePositivity.EInfinity.Hammock.lengthStagePushout_isColimit,
      `SerrePositivity.EInfinity.Hammock.lengthStage_isPushout,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockStageBoundarySum,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockStageTopSum,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockStageBoundarySumInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockStageBoundaryAttach,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockStageTopInclusion,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockStageBoundaryAttach_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockStageTopInclusion_fac,
      `SerrePositivity.EInfinity.BarrattEccles.algebraHammockLengthStage_isPushout,
      `SerrePositivity.EInfinity.Hammock.StageAttachmentData.mk,
      `SerrePositivity.EInfinity.Hammock.StageAttachmentData.lower,
      `SerrePositivity.EInfinity.Hammock.StageAttachmentData.upper,
      `SerrePositivity.EInfinity.Hammock.StageAttachmentData.boundary]

-- EInfinity の全宣言の推移的な公理依存を監査する。
open Lean in
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless (`SerrePositivity.EInfinity).isPrefixOf mod do continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax ↦
      !(#[``propext, ``Classical.choice, ``Quot.sound].contains ax)
    unless unexpected.isEmpty do
      throwError "非標準公理への依存: {name}: {unexpected}"
    declarations := declarations + 1
  if declarations == 0 then throwError "監査対象の EInfinity 宣言がありません"
  unless env.contains `SerrePositivity.EInfinity.projectiveModelCategory do
    throwError "射影モデル構造の宣言がありません"
  for batch in #[e2RequiredBatch0, e2RequiredBatch1, e2RequiredBatch2, e2RequiredBatch3,
      e2RequiredBatch4, e2RequiredBatch5, e2RequiredBatch6, e2RequiredBatch7,
      e2RequiredBatch8, e2RequiredBatch9, e2RequiredBatch10, e2RequiredBatch11,
      e2RequiredBatch12, e2RequiredBatch13, e2RequiredBatch14, e2RequiredBatch15,
      e2RequiredBatch16, e2RequiredBatch17, e2RequiredBatch18, e2RequiredBatch19,
      e2RequiredBatch20, e2RequiredBatch21, e2RequiredBatch22, e2RequiredBatch23,
      e2RequiredBatch24, e2RequiredBatch25, e2RequiredBatch26, e2RequiredBatch27,
      e2RequiredBatch28, e2RequiredBatch29, e2RequiredBatch30, e2RequiredBatch31,
      e2RequiredBatch32, e2RequiredBatch33, e2RequiredBatch34] do
    for required in batch do
      unless env.contains required do
        throwError "EInfinity の必要な宣言がありません: {required}"
  logInfo m!"EInfinity 公理監査成功: {declarations} 宣言。標準 3 公理のみ。"

-- BF §1.2.3 の符号・五項の削除式と零 arity の境界例を照合する。
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SerrePositivity.EInfinity.Surjection

private def bfWord : Fin 7 → Fin 4 := ![0, 2, 1, 0, 3, 1, 0]
example : Function.Surjective bfWord ∧ Nondegenerate bfWord := by decide
example : (fun i => deletionCoefficient bfWord i) = ![1, 0, -1, 1, 0, 1, -1] := by decide
example : Fintype.card (BasisWord 3 0) = 6 := by decide
example : Fintype.card (BasisWord 0 0) = 1 := by decide
example : Fintype.card (BasisWord 0 1) = 0 := by decide
example : Fintype.card (BasisWord 1 1) = 0 := by decide
example : differentialOnWord ℤ (⟨bfWord, by decide⟩ : BasisWord 4 3) =
    generator ℤ ![2, 1, 0, 3, 1, 0] - generator ℤ ![0, 2, 0, 3, 1, 0] +
      generator ℤ ![0, 2, 1, 3, 1, 0] + generator ℤ ![0, 2, 1, 0, 3, 0] -
      generator ℤ ![0, 2, 1, 0, 3, 1] := by
  have hs : (fun i => deletionCoefficient bfWord i) = ![1, 0, -1, 1, 0, 1, -1] := by decide
  have h0 : erase bfWord 0 = ![2, 1, 0, 3, 1, 0] := by decide
  have h2 : erase bfWord 2 = ![0, 2, 0, 3, 1, 0] := by decide
  have h3 : erase bfWord 3 = ![0, 2, 1, 3, 1, 0] := by decide
  have h5 : erase bfWord 5 = ![0, 2, 1, 0, 3, 0] := by decide
  have h6 : erase bfWord 6 = ![0, 2, 1, 0, 3, 1] := by decide
  unfold differentialOnWord
  dsimp only
  simp_rw [congrFun hs]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, one_zsmul, zero_zsmul, neg_one_zsmul, zero_add]
  erw [h0, h2, h3, h5, h6]
  simp only [sub_eq_add_neg, add_assoc]

-- BF §1.3.1 の table の二項と他の行長の選択の退化を照合する。
open SerrePositivity.EInfinity SerrePositivity.EInfinity.TableReduction
private def bfTable : Fin 3 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 1 3, Equiv.swap 2 3]
private def bfSchedule₁ : Schedule 4 2 := ⟨![2, 1, 3], by decide⟩
private def bfSchedule₂ : Schedule 4 2 := ⟨![2, 2, 2], by decide⟩
example : reduceRows (rows bfTable bfSchedule₁) [] = some [0, 1, 3, 1, 3, 2] := by decide
example : reduceRows (rows bfTable bfSchedule₂) [] = some [0, 1, 3, 2, 1, 2] := by decide
example : ∀ r : Schedule 4 2,
    (match reduceRows (rows bfTable r) [] with
    | none => true
    | some xs => !((xs.zip xs.tail).all (fun p => p.1 != p.2)) ||
        xs == [0, 1, 3, 1, 3, 2] || xs == [0, 1, 3, 2, 1, 2]) = true := by decide
example : Fintype.card {r : Schedule 4 2 //
    reduceRows (rows bfTable r) [] = some [0, 1, 3, 1, 3, 2]} = 1 := by decide
example : Fintype.card {r : Schedule 4 2 //
    reduceRows (rows bfTable r) [] = some [0, 1, 3, 2, 1, 2]} = 1 := by decide

-- BF §1.4.2 の復元候補の具体例と table の唯一の非退化出力を照合する。
open SerrePositivity.EInfinity.Surjection SerrePositivity.EInfinity.TableReduction
private def canonicalFixture : BasisWord 4 2 := ⟨![0, 1, 3, 1, 3, 2], by decide⟩
example : rowStarts canonicalFixture = [0, 2, 3] := by decide
example : List.ofFn (fun i : Fin 3 =>
    List.ofFn (fun j => (canonicalVertices canonicalFixture i)⁻¹ j)) =
      [[0, 1, 3, 2], [0, 3, 1, 2], [0, 1, 3, 2]] := by
  simp only [canonicalVertices, canonicalPermutation_inv_list]
  decide
private def canonicalFixtureRows (r : Schedule 4 2) : List (List (Fin 4) × ℕ) :=
  List.ofFn (fun i =>
    (canonicalRow (List.ofFn canonicalFixture.val) (rowStart canonicalFixture i), (r.val i).val))
example : ∀ r : Schedule 4 2,
    (match reduceRows (canonicalFixtureRows r) [] with
    | none => true
    | some xs => !((xs.zip xs.tail).all (fun p => p.1 != p.2)) ||
        xs == [0, 1, 3, 1, 3, 2]) = true := by decide
example : Fintype.card {r : Schedule 4 2 //
    reduceRows (canonicalFixtureRows r) [] = some [0, 1, 3, 1, 3, 2]} = 1 := by decide

-- 最終末尾の相殺例。正しい削除後次数で元の項が非零であることも照合する。
private def terminalWord : BasisWord 2 0 := ⟨![0, 1], by decide⟩
private def terminalTable : Fin 2 → Equiv.Perm (Fin 2) := ![1, Equiv.swap 0 1]
private def terminalSchedule : Schedule 2 1 := ⟨![1, 2], by decide⟩
example : reduceRows (rows terminalTable terminalSchedule) [] = some [0, 1, 0] := by decide
example : reduceRows (rows terminalTable
    (deletionScheduleTransfer terminalSchedule 1 0 (by decide) (by decide))) [] =
      some [0, 1, 1] := by decide
private theorem terminalDeletionTerm_eq_neg :
    listDeletionTerm ℤ (d := 0) ([0, 1, 0] : List (Fin 2)) ⟨2, by decide⟩ =
    -listGenerator ℤ (d := 0) [0, 1] := by
  unfold listDeletionTerm
  have hc : deletionCoefficient
      (fun j : Fin ([0, 1, 0] : List (Fin 2)).length => ([0, 1, 0] : List (Fin 2))[j.val])
      ⟨2, by decide⟩ = -1 := by decide
  rw [hc]
  exact neg_one_zsmul _
example : listDeletionTerm ℤ (d := 0) ([0, 1, 0] : List (Fin 2)) ⟨2, by decide⟩ ≠ 0 := by
  have hv : List.ofFn terminalWord.val = ([0, 1] : List (Fin 2)) := by decide
  have hg : listGenerator ℤ (d := 0) [0, 1] = basis ℤ 2 0 (ULift.up terminalWord) := by
    rw [← hv, listGenerator_ofFn, generator_word]
  rw [terminalDeletionTerm_eq_neg, hg]
  exact neg_ne_zero.mpr ((basis ℤ 2 0).ne_zero _)

example : listDeletionTerm ℤ (d := 0) ([0, 1, 0] : List (Fin 2)) ⟨2, by decide⟩ +
    listDeletionTerm ℤ (d := 0) ([0, 1, 1] : List (Fin 2)) ⟨1, by decide⟩ = 0 := by
  rw [terminalDeletionTerm_eq_neg]
  have hc : deletionCoefficient
      (fun j : Fin ([0, 1, 1] : List (Fin 2)).length => ([0, 1, 1] : List (Fin 2))[j.val])
      ⟨1, by decide⟩ = 1 := by decide
  simp only [listDeletionTerm, hc, one_zsmul]
  exact neg_add_cancel _

-- 逆探索の通過・内部停止・最終延長停止を具体的な行で照合する。
private def releaseSkipRows : List (List (Fin 3) × ℕ) := [([1, 0, 2], 1), ([2, 0, 1], 2)]
example : ReleaseSearch (0 : Fin 3) releaseSkipRows [] [([1, 0, 2], 1)] [[1]] []
    ([2, 0, 1], 2) [] := by
  exact .skip (by decide) (by decide) (by decide) (.hit (by decide))
example : reduceRows releaseSkipRows [0] = some [1, 2, 1] := by decide
example : reduceRows [([1, 0, 2], 1), ([2, 0, 1], 3)] ([] : List (Fin 3)) =
    some [1, 2, 0, 1] := by decide
example : ([1, 2, 0, 1] : List (Fin 3)).eraseIdx 2 = [1, 2, 1] := by decide
example : ReleaseSearch (0 : Fin 2) [([1, 0], 1)] [] [] [] [] ([1, 0], 1) [] := by
  exact .terminal (by decide) (by decide)
example : reduceRows [([1, 0], 1)] ([0] : List (Fin 2)) = some [1] := by decide
example : reduceRows [([1, 0], 2)] ([] : List (Fin 2)) = some [1, 0] := by decide

-- 実際の逆 Schedule の入力は退化出力の残余行末も含む。
private def reverseTerminalSchedule : Schedule 2 1 := ⟨![2, 1], by decide⟩
example : Nonempty (ReverseTransferData terminalTable reverseTerminalSchedule
    [0, 1, 1] ⟨1, by decide⟩) := by
  apply reverseTransferData_nonempty terminalTable reverseTerminalSchedule
    [0, 1, 1] (by decide) ⟨1, by decide⟩ (by decide) (by decide)
example : reduceRows (rows terminalTable
    (deletionScheduleTransfer reverseTerminalSchedule 0 1 (by decide) (by decide))) [] =
      some [0, 1, 0] := by decide

-- 一般の全単射・全残余相殺・微分保存・平方零を具体例でも元の型で適用する。
noncomputable example : FinalDeletion bfTable ≃ CaesuraDeletion bfTable := deletionEquiv bfTable
example : (∑ r : Schedule 4 2, remainderTerm ℤ bfTable r) = 0 :=
  sum_remainderTerm_zero ℤ bfTable
example : Surjection.differential ℤ 4 1 (onSequence ℤ bfTable) = vertexBoundary ℤ bfTable :=
  differential_onSequence_eq_vertexBoundary ℤ bfTable
example : (Surjection.differential ℤ 4 0).comp (Surjection.differential ℤ 4 1) = 0 :=
  differential_comp_differential ℤ 4 0
example : (chainMap ℤ 0).f 1 = ModuleCat.ofHom (normalizedMap ℤ 0 1) := chainMap_f ℤ 0 1

-- BF §1.2.6 の三つの合成語と符号 +,−,− を零始まりで照合する。
private def compositionOuter : BasisWord 3 1 := ⟨![0, 1, 0, 2], by decide⟩
private def compositionInner : BasisWord 2 1 := ⟨![0, 1, 0], by decide⟩
private def compositionCut₁ : OverlapPartition (occurrenceCount compositionOuter.val 0) 3 := by
  change OverlapPartition 2 3
  exact ⟨![1, 3], by decide⟩
private def compositionCut₂ : OverlapPartition (occurrenceCount compositionOuter.val 0) 3 := by
  change OverlapPartition 2 3
  exact ⟨![2, 2], by decide⟩
private def compositionCut₃ : OverlapPartition (occurrenceCount compositionOuter.val 0) 3 := by
  change OverlapPartition 2 3
  exact ⟨![3, 1], by decide⟩
example : Fintype.card (OverlapPartition 2 3) = 3 := by decide
example : compositeWord compositionOuter compositionInner 0 compositionCut₁ =
    [0, 2, 0, 1, 0, 3] := by decide
example : compositeWord compositionOuter compositionInner 0 compositionCut₂ =
    [0, 1, 2, 1, 0, 3] := by decide
example : compositeWord compositionOuter compositionInner 0 compositionCut₃ =
    [0, 1, 0, 2, 0, 3] := by decide
example : compositionSign compositionOuter compositionInner 0 compositionCut₁ = 1 := by decide
example : compositionSign compositionOuter compositionInner 0 compositionCut₂ = -1 := by decide
example : compositionSign compositionOuter compositionInner 0 compositionCut₃ = -1 := by decide
example : Fintype.card (OverlapPartition 2 0) = 0 := by decide
private def emptyCompositionWord : BasisWord 0 0 := ⟨Fin.elim0, by decide⟩
example : compositionOnWords ℤ compositionInner emptyCompositionWord 0 = 0 :=
  compositionOnWords_nullary_of_count_ne_one ℤ _ _ _ (by decide)
example : Surjection.partialComposition ℤ 2 2 1 1 0
    (basis ℤ 3 1 (ULift.up compositionOuter))
    (basis ℤ 2 1 (ULift.up compositionInner)) =
      compositionOnWords ℤ compositionOuter compositionInner 0 :=
  partialComposition_basis ℤ _ _ _

-- BF §1.5.4–6 の候補経路が、三項の合成語と同じ符号を持つ。
example :
    ((compositionPath compositionOuter compositionInner 0 compositionCut₁).sign : ℤ) = 1 := by
  rw [compositionPath_sign]
  decide
example :
    ((compositionPath compositionOuter compositionInner 0 compositionCut₂).sign : ℤ) = -1 := by
  rw [compositionPath_sign]
  decide
example :
    ((compositionPath compositionOuter compositionInner 0 compositionCut₃).sign : ℤ) = -1 := by
  rw [compositionPath_sign]
  decide
example : compositeGenerator ℤ compositionOuter compositionInner 0 compositionCut₁ =
    basis ℤ 4 2 (ULift.up (compositeBasisWord compositionOuter compositionInner 0 compositionCut₁
      (by decide))) := compositeGenerator_eq_basis ℤ _ _ _ _ (by decide)
example : (∑ i : Fin 2, segmentDegree compositionInner.val compositionCut₂ i) = 1 :=
  sum_segmentDegree compositionInner compositionCut₂ (by decide)
example : (∑ i : Fin 3, outerSegmentDegree compositionOuter.val 0 i.val) = 1 :=
  sum_outerSegmentDegree compositionOuter 0

-- 内外の非自明な逆置換行と除外文字、および空の内側行を照合する。
private def rowOuter : Equiv.Perm (Fin 3) := Equiv.swap 0 2
private def rowInner : Equiv.Perm (Fin 2) := Equiv.swap 0 1
example : List.ofFn rowOuter.symm = [2, 1, 0] := by decide
example : List.ofFn rowInner.symm = [1, 0] := by decide
example : substitute (n := 2) (1 : Fin 3) [2, 1, 0] [[1, 0]] = [3, 2, 1, 0] := by
  decide
example : available (compositionRemoved (1 : Fin 3) [2] [1])
    (List.ofFn (BarrattEccles.permutationComposition 2 2 1 rowOuter rowInner).symm) =
      [1, 0] := by
  rw [permutationComposition_available_substitute rowOuter rowInner 1 [2] [1] (by decide)]
  decide
example : List.ofFn
    (BarrattEccles.permutationComposition 2 0 1 rowOuter (1 : Equiv.Perm (Fin 0))).symm =
      [1, 0] := by
  rw [permutationComposition_inverse_row_substitute rowOuter (1 : Equiv.Perm (Fin 0)) 1]
  decide

-- 三種類の実際の二行抽出で、選択行の末尾を次行に残すことを確認する。
private def rowPre : List {a : Fin 3 // a ≠ 1} := [⟨2, by decide⟩]
private def rowPost : List {a : Fin 3 // a ≠ 1} := [⟨0, by decide⟩]
private def rowComposite : List (Fin 4) :=
  List.ofFn (BarrattEccles.permutationComposition 2 2 1 rowOuter rowInner).symm
private lemma rowComposite_available :
    available (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) rowComposite =
      substitute 1 (rowPre.map Subtype.val ++ 1 :: rowPost.map Subtype.val) [[1, 0]] := by
  rw [rowComposite, permutationComposition_state_available_substitute]
  decide
example : reduceRows [(rowComposite, 1), (rowComposite, 1)]
    (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) = some [3, 3] := by
  exact compositionExtractionStep_before (m := 2) (n := 2)
    1 [] [] [1, 0] rowPre rowPost rowComposite 1
    [(rowComposite, 1)] [3] rowComposite_available (by decide) (by decide) (by decide)
example : reduceRows [(rowComposite, rowPre.length + 2), (rowComposite, 1)]
    (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) = some [3, 2, 1, 1] := by
  exact compositionExtractionStep_inside (m := 2) (n := 2)
    1 [] [] [1, 0] rowPre rowPost rowComposite 2
    [(rowComposite, 1)] [1] rowComposite_available (by decide) (by decide) (by decide)
example : reduceRows [(rowComposite, rowPre.length + 2 + 1), (rowComposite, 1)]
    (compositionStateRemoved (1 : Fin 3) [] ([] : List (Fin 2))) = some [3, 2, 1, 0, 0] := by
  exact compositionExtractionStep_after (m := 2) (n := 2)
    1 [] [] [1, 0] rowPre rowPost rowComposite 1
    [(rowComposite, 1)] [0] rowComposite_available (by decide) (by decide)
    (by intro b; fin_cases b <;> decide) (by decide)
example : available (compositionStateRemoved (1 : Fin 3) [1] ([] : List (Fin 2)))
    rowComposite = [3, 0] := by
  rw [rowComposite, permutationComposition_state_available_substitute]
  decide

-- BF の実際の成功表の行末・一文字行・最終行と、同じ行を共有する成分端点を照合する。
private lemma rankFixture_success :
    reduceRows (rows bfTable bfSchedule₁) [] = some (List.ofFn canonicalFixture.val) := by
  decide
example : lineRank canonicalFixture.val (scheduleOffset bfSchedule₁ 0 + 1) = 0 :=
  lineRank_schedule_of_reduction bfTable bfSchedule₁ canonicalFixture.val
    rankFixture_success 0 1 (by decide)
example : lineRank canonicalFixture.val (scheduleOffset bfSchedule₁ 1 + 0) = 1 :=
  lineRank_schedule_of_reduction bfTable bfSchedule₁ canonicalFixture.val
    rankFixture_success 1 0 (by decide)
example : lineRank canonicalFixture.val (scheduleOffset bfSchedule₁ 2 + 2) = 2 :=
  lineRank_schedule_of_reduction bfTable bfSchedule₁ canonicalFixture.val
    rankFixture_success 2 2 (by decide)
example : reductionRow bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 2 = 1 := by
  apply (reductionRow_eq_iff bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 2 1).mpr
  decide
private def rankFixtureCuts : OverlapPartition 2 6 := ⟨![3, 4], by decide⟩
example : segmentDegree canonicalFixture.val rankFixtureCuts 0 = 1 := by
  rw [segmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0]
  decide
example : segmentDegree canonicalFixture.val rankFixtureCuts 1 = 1 := by
  rw [segmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 1]
  decide
-- 隣接重複を含む成功出力でも行内位置の番号は同じ定理で計算する。
private def rankDegenerate : Fin 3 → Fin 2 := ![0, 1, 1]
example : lineRank rankDegenerate (scheduleOffset reverseTerminalSchedule 0 + 1) = 0 := by
  exact lineRank_schedule_of_reduction terminalTable reverseTerminalSchedule rankDegenerate
    (by decide) 0 1 (by decide)
example : lineRank rankDegenerate (scheduleOffset reverseTerminalSchedule 1 + 0) = 1 := by
  exact lineRank_schedule_of_reduction terminalTable reverseTerminalSchedule rankDegenerate
    (by decide) 1 0 (by decide)

example : outerSegmentDegree canonicalFixture.val 1 0 = 0 := by
  rw [outerSegmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 0]
  decide
example : outerSegmentDegree canonicalFixture.val 1 1 = 2 := by
  rw [outerSegmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 1]
  decide
example : outerSegmentDegree canonicalFixture.val 1 2 = 0 := by
  rw [outerSegmentDegree_eq_reductionRows bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 2]
  decide

example : StrictMono (fun j : Fin (occurrenceCount canonicalFixture.val 1) =>
    reductionRow bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceAt canonicalFixture.val 1 j)) :=
  occurrence_reductionRow_strictMono bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 1
example : lineRank rankDegenerate 1 < lineRank rankDegenerate 2 := by
  have h : reduceRows (rows terminalTable reverseTerminalSchedule) [] =
      some (List.ofFn rankDegenerate) := by decide
  exact reductionRow_lt_of_repeat terminalTable reverseTerminalSchedule rankDegenerate h
    1 2 (by decide) (by decide)

-- 同じ元の成功から取り出した隣接 cursor は、実際の末尾以外の除外更新で接続する。
private noncomputable def cursorRowOne :
    ScheduleRowCursor bfTable bfSchedule₁ 1 (List.ofFn canonicalFixture.val) :=
  Classical.choice (scheduleRowCursor_nonempty bfTable bfSchedule₁ 1
    (List.ofFn canonicalFixture.val) rankFixture_success)
private noncomputable def cursorRowTwo :
    ScheduleRowCursor bfTable bfSchedule₁ 2 (List.ofFn canonicalFixture.val) :=
  Classical.choice (scheduleRowCursor_nonempty bfTable bfSchedule₁ 2
    (List.ofFn canonicalFixture.val) rankFixture_success)
example : cursorRowTwo.removed = cursorRowOne.removed ++
    (available cursorRowOne.removed (vertexRow bfTable 1)).take ((bfSchedule₁.val 1).val - 1) :=
  (ScheduleRowCursor.next_state 1 cursorRowOne cursorRowTwo).2
example : (available cursorRowTwo.removed (vertexRow bfTable 2))[1]'(by
    have := cursorRowTwo.bound; change 3 ≤ _ at this; omega) = 3 := by
  have h := cursorRowTwo.value (4 : Fin 6) ⟨1, by decide⟩ (by decide)
  exact h.symm.trans (by decide)
-- 元の第三行の内部からの再開と、同じ行の末尾からの再開を元の出力の末尾で検証する。
example : reduceRows ((vertexRow bfTable 2, 2) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 1) =
      some [3, 2] := by
  have h := cursorRowTwo.remainder_success_eq_drop (4 : Fin 6) ⟨1, by decide⟩ (by decide)
  change reduceRows ((vertexRow bfTable 2, 2) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 1) =
      some ((List.ofFn canonicalFixture.val).drop 4) at h
  have ho : (List.ofFn canonicalFixture.val).drop 4 = [3, 2] := by decide
  rw [ho] at h
  exact h
example : reduceRows ((vertexRow bfTable 2, 1) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 2) =
      some [2] := by
  have h := cursorRowTwo.remainder_success_eq_drop (5 : Fin 6) ⟨2, by decide⟩ (by decide)
  change reduceRows ((vertexRow bfTable 2, 1) :: cursorRowTwo.after)
    (cursorRowTwo.removed ++ (available cursorRowTwo.removed (vertexRow bfTable 2)).take 2) =
      some ((List.ofFn canonicalFixture.val).drop 5) at h
  have ho : (List.ofFn canonicalFixture.val).drop 5 = [2] := by decide
  rw [ho] at h
  exact h
example : canonicalFixture.val 4 ∉
    (reductionCursor bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 4).removed :=
  reductionCursor_value_not_removed bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 4

-- BF の元の成功表から、二つの重なる複数行成分を追加の成功仮定なしに抽出する。
example : reduceRows
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 0).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (rankFixtureCuts.startPosition (by decide) 0)) = some [0, 1, 3] := by
  have h := componentExtraction_success bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0
  have hw : rankFixtureCuts.segment canonicalFixture.val 0 = [0, 1, 3] := by decide
  rw [hw] at h
  exact h
example : reduceRows
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 1).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (rankFixtureCuts.startPosition (by decide) 1)) = some [3, 1, 3, 2] := by
  have h := componentExtraction_success bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 1
  have hw : rankFixtureCuts.segment canonicalFixture.val 1 = [3, 1, 3, 2] := by decide
  rw [hw] at h
  exact h
example : (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).part.length = 2 := by
  rw [componentExtraction_length]
  decide
-- 終成分が同じ元の最終行内に入る切断も、同じ構成で一行の成功証跡になる。
private def sameRowCuts : OverlapPartition 2 6 := ⟨![5, 2], by decide⟩
example : reduceRows
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      sameRowCuts (by decide) 1).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (sameRowCuts.startPosition (by decide) 1)) = some [3, 2] := by
  have h := componentExtraction_success bfTable bfSchedule₁ canonicalFixture rankFixture_success
    sameRowCuts (by decide) 1
  have hw : sameRowCuts.segment canonicalFixture.val 1 = [3, 2] := by decide
  rw [hw] at h
  exact h
example : (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    sameRowCuts (by decide) 1).part.length = 1 := by
  rw [componentExtraction_length]
  decide
-- 共有端点の状態を厳密に引き継ぎ、共有文字を両成分に含めたまま連結する。
example : reduceRows
    ((componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 0).part ++
    (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      rankFixtureCuts (by decide) 1).part)
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (rankFixtureCuts.startPosition (by decide) 0)) = some [0, 1, 3, 3, 1, 3, 2] := by
  have ht := componentExtraction_adjacent_prefix bfTable bfSchedule₁ canonicalFixture
    rankFixture_success rankFixtureCuts (by decide) 0 1 (by decide)
  have hs := ht.append [] [] rfl
  simp only [List.append_nil, List.flatten_append, componentExtraction_word] at hs
  have hw : rankFixtureCuts.segment canonicalFixture.val 0 ++
      rankFixtureCuts.segment canonicalFixture.val 1 = [0, 1, 3, 3, 1, 3, 2] := by decide
  rw [hw] at hs
  exact hs
example : (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).part.map Prod.fst =
      [vertexRow bfTable 0, vertexRow bfTable 1] := by
  have hs := (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).source
  change (componentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    rankFixtureCuts (by decide) 0).part.map Prod.fst =
      (((rows bfTable bfSchedule₁).drop 0).take 2).map Prod.fst at hs
  have hw : (((rows bfTable bfSchedule₁).drop 0).take 2).map Prod.fst =
      [vertexRow bfTable 0, vertexRow bfTable 1] := by decide
  exact hs.trans hw

-- 指定値の二出現の間の外側成分は、元の三行全てを通って実際の部分語を返す。
example : reduceRows
    (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      1 (by decide) 1).part
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceBoundaryPosition canonicalFixture.val 1 (by decide) 1)) = some [1, 3, 1] := by
  have h := outerComponentExtraction_success bfTable bfSchedule₁ canonicalFixture
    rankFixture_success 1 (by decide) 1
  have hw : outerComponentWord canonicalFixture.val 1 1 = [1, 3, 1] := by decide
  rw [hw] at h
  exact h
example : (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
    1 (by decide) 1).part.length = 3 := by
  rw [outerComponentExtraction_length]
  decide

-- 元の内側成功表と元の外側の指定出現から、垂直成分を実際の合成行列で抽出する。
private lemma verticalInner_success : reduceRows (rows terminalTable terminalSchedule) [] =
    some (List.ofFn compositionInner.val) := by decide
private def verticalCuts : OverlapPartition 2 3 := ⟨![2, 2], by decide⟩
private noncomputable def verticalFirstBlock : List (List (Fin 5) × ℕ) :=
  fixedOuterRows (m := 3) (n := 2)
    (bfTable (reductionRow bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 1)) 1
    (componentExtraction terminalTable terminalSchedule compositionInner verticalInner_success
      verticalCuts (by decide) 0).weightedVertices
private noncomputable def verticalFirstInitial : List (Fin 5) :=
  compositionStateRemoved (m := 3) (n := 2) 1
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success 1)
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success
      (verticalCuts.startPosition (by decide) 0))
example : reduceRows verticalFirstBlock verticalFirstInitial = some [1, 2] := by
  have h := componentVerticalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1 1 (by decide)
    terminalTable terminalSchedule compositionInner verticalInner_success
    verticalCuts (by decide) 0 [] [] rfl
  have hw : (verticalCuts.segment compositionInner.val 0).map
      (BarrattEccles.insertedPosition 3 2 1) = [1, 2] := by decide
  simpa only [verticalFirstBlock, verticalFirstInitial, List.append_nil, hw] using h

-- 共有頂点の同じ二行を融合すると、共有文字は一度だけ出力し、元の後続状態へつながる。
example : reduceRows [([0, 1, 2, 3], 4), ([3], 1)] ([] : List (Fin 4)) =
    some [0, 1, 2, 3, 3] := by
  have h := rowFusion_success ([] : List (Fin 4)) [0, 1, 2, 3] (by decide) 2 3
    (by decide) (by decide) (by decide) (by decide) [([3], 1)] [3] (by decide)
  exact h

-- 未選択の内側文字が残る状態で、元の外側の零次数・正次数の水平成分を抽出する。
private noncomputable def horizontalFixtureBlock
    (i : Fin (occurrenceCount canonicalFixture.val 1)) : List (List (Fin 5) × ℕ) :=
  fixedInnerRows (m := 3) (n := 2)
    (terminalTable (reductionRow terminalTable terminalSchedule compositionInner.val
      verticalInner_success 0)) 1
    (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      1 (by decide) i.val).weightedVertices
private noncomputable def horizontalFixtureInitial
    (i : Fin (occurrenceCount canonicalFixture.val 1)) : List (Fin 5) :=
  compositionStateRemoved (m := 3) (n := 2) 1
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceBoundaryPosition canonicalFixture.val 1 (by decide) i.val))
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success 0)
example : reduceRows (horizontalFixtureBlock ⟨0, by decide⟩)
    (horizontalFixtureInitial ⟨0, by decide⟩) = some [0, 1] := by
  have h := componentHorizontalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1 ⟨0, by decide⟩
    terminalTable terminalSchedule compositionInner verticalInner_success 0 [] [] rfl
  have hw : (outerComponentWord canonicalFixture.val 1 0).map
      (horizontalLabel (m := 3) (n := 2) 1 (compositionInner.val 0)) = [0, 1] := by decide
  simpa only [horizontalFixtureBlock, horizontalFixtureInitial, List.append_nil, hw] using h
example : reduceRows (horizontalFixtureBlock ⟨1, by decide⟩)
    (horizontalFixtureInitial ⟨1, by decide⟩) =
    some [1, 4, 1] := by
  have h := componentHorizontalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1 ⟨1, by decide⟩
    terminalTable terminalSchedule compositionInner verticalInner_success 0 [] [] rfl
  have hw : (outerComponentWord canonicalFixture.val 1 1).map
      (horizontalLabel (m := 3) (n := 2) 1 (compositionInner.val 0)) = [1, 4, 1] := by decide
  simpa only [horizontalFixtureBlock, horizontalFixtureInitial, List.append_nil, hw] using h

-- 元の内側成功表の最終位置では未選択の内側文字がなく、末尾一文字だけが残る。
example : available
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success 2)
    (List.ofFn (terminalTable (reductionRow terminalTable terminalSchedule compositionInner.val
      verticalInner_success 2)).symm) = [0] := by
  have h := reductionRemoved_last_singleton terminalTable terminalSchedule compositionInner
    verticalInner_success 2 (by decide)
  have hv : compositionInner.val 2 = 0 := by decide
  rw [hv] at h
  exact h
private noncomputable def finalHorizontalBlock : List (List (Fin 5) × ℕ) :=
  fixedInnerRows (m := 3) (n := 2)
    (terminalTable (reductionRow terminalTable terminalSchedule compositionInner.val
      verticalInner_success 2)) 1
    (outerComponentExtraction bfTable bfSchedule₁ canonicalFixture rankFixture_success
      1 (by decide) (occurrenceCount canonicalFixture.val 1)).weightedVertices
private noncomputable def finalHorizontalInitial : List (Fin 5) :=
  compositionStateRemoved (m := 3) (n := 2) 1
    (reductionRemoved bfTable bfSchedule₁ canonicalFixture.val rankFixture_success
      (occurrenceBoundaryPosition canonicalFixture.val 1 (by decide)
        (occurrenceCount canonicalFixture.val 1)))
    (reductionRemoved terminalTable terminalSchedule compositionInner.val verticalInner_success 2)
example : reduceRows finalHorizontalBlock finalHorizontalInitial = some [1, 4, 3] := by
  have h := finalHorizontalExtraction_success (m := 3) (n := 2)
    bfTable bfSchedule₁ canonicalFixture rankFixture_success 1
    terminalTable terminalSchedule compositionInner verticalInner_success 2 (by decide) [] [] rfl
  have hw : (outerComponentWord canonicalFixture.val 1 (occurrenceCount canonicalFixture.val 1)).map
      (horizontalLabel (m := 3) (n := 2) 1 (compositionInner.val 2)) = [1, 4, 3] := by decide
  simpa only [finalHorizontalBlock, finalHorizontalInitial, List.append_nil, hw] using h
-- 指定値を行内部で最終除外し、最後の内側文字も除外した状態で後続へ接続する。
example : reduceRows
    [(List.ofFn (BarrattEccles.permutationComposition 2 2 1 1 rowInner).symm, 3), ([1, 3], 1)]
    (compositionStateRemoved (m := 2) (n := 2) 1 [] [1]) = some [0, 1, 3, 3] := by
  have h := singletonHorizontalStep_success (m := 2) (n := 2)
    1 rowInner 1 [] [1] 0 (by decide) 3 (by decide) (by decide) [([1, 3], 1)] [3] (by decide)
  exact h
-- 元の表の途中の共有行も同じ位置計算で融合し、先行出力は保つ。
example : reduceRows [([4], 1), ([0, 1, 2, 3], 4), ([3], 1)] ([] : List (Fin 5)) =
    some [4, 0, 1, 2, 3, 3] := by
  have h : reduceRows ([([4], 1)] ++
      ([0, 1, 2, 3], 2) :: ([0, 1, 2, 3], 3) :: [([3], 1)]) ([] : List (Fin 5)) =
        some [4, 0, 1, 1, 2, 3, 3] := by decide
  exact rowFusion_in_context [([4], 1)] [] [0, 1, 2, 3] (by decide) 2 3 [([3], 1)]
    [4, 0, 1, 1, 2, 3, 3] h

-- 元の二つの成功だけから、全ての水平・垂直成分を含む表の成功を導く。
private def fullCompositionFixture : TableCompositionData 3 2 2 1 where
  outer := bfTable
  outerSchedule := bfSchedule₁
  outerWord := canonicalFixture
  outer_success := rankFixture_success
  inner := terminalTable
  innerSchedule := terminalSchedule
  innerWord := compositionInner
  inner_success := verticalInner_success
  slot := 1
  cuts := by change OverlapPartition 2 3; exact verticalCuts
  inner_positive := by decide
example : reduceRows (fullCompositionFixture.rawRows 0) [] =
    some [0, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3] := by
  have hw : fullCompositionFixture.rawWord 0 = [0, 1, 1, 2, 2, 4, 2, 2, 1, 1, 4, 3] := by
    rw [TableCompositionData.rawWord,
      dite_eq_left (show 0 < fullCompositionFixture.count by decide),
      TableCompositionData.rawWord, dite_eq_left (show 1 < fullCompositionFixture.count by decide),
      TableCompositionData.rawWord,
      dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
    decide
  simpa only [hw] using fullCompositionFixture.raw_success_zero

-- 全表の両種類の共有境界は、元の成功表の同じ実際の置換行を共有する。
example : ((fullCompositionFixture.horizontalRows 0).map Prod.fst).getLast? =
    ((fullCompositionFixture.verticalRows ⟨0, by decide⟩).map Prod.fst).head? :=
  fullCompositionFixture.horizontal_vertical_join ⟨0, by decide⟩
example : ((fullCompositionFixture.verticalRows ⟨1, by decide⟩).map Prod.fst).getLast? =
    ((fullCompositionFixture.horizontalRows 2).map Prod.fst).head? :=
  fullCompositionFixture.vertical_horizontal_join ⟨1, by decide⟩

-- 全共有行の融合後は、四つの重複境界文字を消した実際の合成語を返す。
private lemma fusedFixture_word : fullCompositionFixture.fusedWord 0 =
    [0, 1, 2, 4, 2, 1, 4, 3] := by
  rw [fullCompositionFixture.fusedWord_step ⟨0, by decide⟩,
    fullCompositionFixture.fusedWord_step ⟨1, by decide⟩,
    TableCompositionData.fusedWord,
    dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
  decide
example : reduceRows (fullCompositionFixture.fusedRows 0) [] =
    some [0, 1, 2, 4, 2, 1, 4, 3] := by
  simpa only [fusedFixture_word] using fullCompositionFixture.fused_success_zero

-- 行長の古典選択を使わず、元の全成分語だけで融合出力を計算する。
private lemma blockFixture_word : fullCompositionFixture.blockWord 0 =
    [0, 1, 2, 4, 2, 1, 4, 3] := by
  rw [TableCompositionData.blockWord,
    dite_eq_left (show 0 < fullCompositionFixture.count by decide),
    TableCompositionData.blockWord,
    dite_eq_left (show 1 < fullCompositionFixture.count by decide),
    TableCompositionData.blockWord,
    dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
  decide
example : reduceRows (fullCompositionFixture.fusedRows 0) [] =
    some [0, 1, 2, 4, 2, 1, 4, 3] := by
  simpa only [blockFixture_word] using fullCompositionFixture.fused_success_blockWord
example : fullCompositionFixture.fusedWord 0 = fullCompositionFixture.blockWord 0 :=
  fullCompositionFixture.fusedWord_eq_blockWord 0 (by decide)
-- 前半が二つの指定値を含むとき、後半は実際に二つの部分語を消費して始まる。
example : substitute (m := 1) (n := 2) 0 ([0, 1, 0] ++ [0, 1]) [[0], [1], [0, 1]] =
    substitute (m := 1) (n := 2) 0 [0, 1, 0] [[0], [1], [0, 1]] ++
      substitute (m := 1) (n := 2) 0 [0, 1] [[0, 1]] := by
  have hc : ([0, 1, 0] : List (Fin 2)).count 0 = 2 := by decide
  have h := substitute_append (m := 1) (n := 2) 0 [0, 1, 0] [0, 1] [[0], [1], [0, 1]]
  rw [hc] at h
  exact h

-- 二番目の指定値以前に一個、自身まで含めると二個の部分語を消費する。
example : ((List.ofFn canonicalFixture.val).take 3).count 1 = 1 := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  simpa only [hp] using occurrenceAt_count_take canonicalFixture.val 1 ⟨1, by decide⟩
example : ((List.ofFn canonicalFixture.val).take 4).count 1 = 2 := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  simpa only [hp] using occurrenceAt_count_take_succ canonicalFixture.val 1 ⟨1, by decide⟩
-- 隣接する出現の間の水平文字は指定値と異なる。
example : canonicalFixture.val 2 ≠ 1 :=
  occurrenceAt_none_between canonicalFixture.val 1 ⟨0, by decide⟩ ⟨1, by decide⟩ rfl 2
    (by decide) (by decide)
-- 第二出現の代入では第二部分語を使い、その後へ残りの部分語を渡す。
example : substitute (n := 2) 1 (List.ofFn canonicalFixture.val) [[0, 1], [1, 0]] =
    substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).take 3) [[0, 1], [1, 0]] ++
      [2, 1] ++ substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).drop 4) [] := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  have h := substitute_at_occurrence (n := 2) canonicalFixture.val 1 ⟨1, by decide⟩
    [[0, 1], [1, 0]]
  rw [hp] at h
  exact h

-- 実際の重なる分割でも、第二出現の挿入部分は同じ番号の垂直語になる。
example : compositeWord canonicalFixture compositionInner 1 verticalCuts =
    substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).take 3)
      (verticalCuts.segments compositionInner.val) ++
        (verticalCuts.segment compositionInner.val ⟨1, by decide⟩).map
          (BarrattEccles.insertedPosition 3 2 1) ++
            substitute (n := 2) 1 ((List.ofFn canonicalFixture.val).drop 4) [] := by
  have hp : (occurrenceAt canonicalFixture.val 1 ⟨1, by decide⟩).val = 3 := by decide
  have h := compositeWord_at_occurrence canonicalFixture compositionInner 1 verticalCuts
    ⟨1, by decide⟩
  rw [hp] at h
  exact h

-- 最初の融合水平部分は、最初の指定値以前の実際の代入と一致する。
example : (fullCompositionFixture.horizontalWord 0).dropLast = [0] := by
  exact fullCompositionFixture.firstHorizontal_dropLast.trans (by decide)

-- 中間・最終水平語と共有垂直末尾を、元の成分から一般定理で計算する。
example : (fullCompositionFixture.horizontalWord 1).dropLast = [2, 4] := by
  exact (fullCompositionFixture.middleHorizontal_dropLast ⟨0, by decide⟩ ⟨1, by decide⟩ rfl).trans
    (by decide)
example : fullCompositionFixture.horizontalWord 2 = [1, 4, 3] := by
  exact (fullCompositionFixture.finalHorizontal_word ⟨1, by decide⟩ (by decide)).trans (by decide)
-- 共有境界を全部融合した実際の表が、元のリスト代入による合成語を返す。
example : fullCompositionFixture.blockWord 0 =
    compositeWord canonicalFixture compositionInner 1 verticalCuts :=
  fullCompositionFixture.blockWord_eq_compositeWord
example : reduceRows (fullCompositionFixture.fusedRows 0) [] =
    some (compositeWord canonicalFixture compositionInner 1 verticalCuts) :=
  fullCompositionFixture.fused_success_compositeWord

-- 次数 2 と次数 1 の元の二表から、融合後は四行・総選択長八の実際の Schedule を得る。
example : (fullCompositionFixture.fusedRows 0).length = 4 :=
  fullCompositionFixture.fusedRows_length
example : (∑ i, fullCompositionFixture.fusedLength i) = 8 :=
  fullCompositionFixture.fusedLength_sum
example : (∑ i, (fullCompositionFixture.fusedSchedule.val i).val) = 8 :=
  fullCompositionFixture.fusedSchedule.property.2
example : ∀ i, 0 < (fullCompositionFixture.fusedSchedule.val i).val :=
  fullCompositionFixture.fusedSchedule.property.1
example (i : Fin 4) : fullCompositionFixture.fusedLength i ≤ 5 :=
  (fullCompositionFixture.fusedLength_bounds i).2

-- 実際の経路連結の共有頂点は一度だけ残る。
example : DegreePath.vertices (DegreePath.append (DegreePath.horizontal 1)
    (DegreePath.vertical 2)) = [(0, 0), (1, 0), (1, 1), (1, 2)] := by
  rw [DegreePath.vertices_append, DegreePath.vertices_horizontal, DegreePath.vertices_vertical]
  decide
example : DegreePath.vertices (DegreePath.corner 0 0) = [(0, 0)] := by
  exact (DegreePath.vertices_corner 0 0).trans (by decide)
-- 最初の水平次数零・後の垂直次数零を含む実際の compositionPath の全頂点。
private lemma compositionFixture_vertices :
    DegreePath.vertices (compositionPath canonicalFixture compositionInner 1 verticalCuts) =
      [(0, 0), (0, 1), (1, 1), (2, 1)] := by
  have hh : outerSegmentDegree canonicalFixture.val 1 0 = 0 := by decide
  have hp : compositionDegreePairs canonicalFixture compositionInner 1 verticalCuts =
      [(1, 2), (0, 0)] := by decide
  have h := compositionPath_vertices canonicalFixture compositionInner 1 verticalCuts
  rw [hh, hp] at h
  apply h.trans
  simp only [DegreePath.blockVertices]
  decide

-- 元の所属行から作った融合格子列は同じ全頂点列を持つ。
private lemma fusedFixture_vertices : fullCompositionFixture.fusedGridVertices 0 =
    [(0, 0), (0, 1), (1, 1), (2, 1)] := by
  rw [TableCompositionData.fusedGridVertices,
    dite_eq_left (show 0 < fullCompositionFixture.count by decide),
    TableCompositionData.fusedGridVertices,
    dite_eq_left (show 1 < fullCompositionFixture.count by decide),
    TableCompositionData.fusedGridVertices,
    dite_eq_right (show ¬2 < fullCompositionFixture.count by decide)]
  decide
-- 具体例では元の実際の経路置換列と構成済み Schedule で抽出成功する。
example : reduceRows (rows fullCompositionFixture.pathSequence fullCompositionFixture.fusedSchedule)
    [] = some (compositeWord canonicalFixture compositionInner 1 verticalCuts) := by
  exact fullCompositionFixture.pathSequence_success

-- 座標の一致は具体例の有限計算に頼らず一般定理からも得られる。
example : DegreePath.vertices (compositionPath canonicalFixture compositionInner 1 verticalCuts) =
    fullCompositionFixture.fusedGridVertices 0 :=
  fullCompositionFixture.compositionPath_vertices_eq_grid
-- 実際の構成済み経路 Schedule の正規化項は、期待した非退化合成語の生成元。
example : term ℤ fullCompositionFixture.pathSequence fullCompositionFixture.fusedSchedule =
    listGenerator ℤ [0, 1, 2, 4, 2, 1, 4, 3] := by
  have h := fullCompositionFixture.term_pathSequence ℤ
  have hw : compositeWord canonicalFixture compositionInner 1 verticalCuts =
      [0, 1, 2, 4, 2, 1, 4, 3] := by decide
  change term ℤ fullCompositionFixture.pathSequence fullCompositionFixture.fusedSchedule =
    listGenerator ℤ (compositeWord canonicalFixture compositionInner 1 verticalCuts) at h
  rw [hw] at h
  exact h

-- 連続重複だけを縮め、離れた同じ値は残す。
example : AdjacentCollapse.collapse ([0, 0, 1, 1, 0, 0] : List (Fin 2)) = [0, 1, 0] := by
  decide
-- 反復出現を含む実際の合成語から元の両語を一般定理で復元する。
example : CompositeRecovery.outerWord 1
    (compositeWord canonicalFixture compositionInner 1 verticalCuts) = [0, 1, 3, 1, 3, 2] := by
  exact (CompositeRecovery.outerWord_compositeWord canonicalFixture compositionInner 1
    verticalCuts (by decide)).trans (by decide)
example : (compositeWord canonicalFixture compositionInner 1 verticalCuts).filterMap
    (CompositeRecovery.innerLabel 1) = [0, 1, 1, 0] := by
  exact (CompositeRecovery.inner_compositeWord canonicalFixture compositionInner 1
    verticalCuts).trans (by decide)
example : CompositeRecovery.innerWord 1
    (compositeWord canonicalFixture compositionInner 1 verticalCuts) = [0, 1, 0] := by
  exact (CompositeRecovery.innerWord_compositeWord canonicalFixture compositionInner 1
    verticalCuts (by decide)).trans (by decide)

-- 出力だけから両分割部分語を共有端点も含めて復元する。
example : CompositeRecovery.partsOfWord 1
    (compositeWord canonicalFixture compositionInner 1 verticalCuts) = [[0, 1], [1, 0]] := by
  exact (CompositeRecovery.partsOfWord_compositeWord canonicalFixture compositionInner 1
    verticalCuts (by decide)).trans (by decide)
-- 分割復元は空の内側部分語もそのまま扱う。
example : CompositeRecovery.splitParts (m := 1) (n := 0) 0 [0, 1] [0] = [[]] := by
  exact CompositeRecovery.splitParts_substitute (m := 1) (n := 0) 0 [0, 1] [[]]
    (by decide) (by decide)
-- 同じ成功出力を与える元の Schedule は一意。
example (r : Schedule 4 2)
    (h : reduceRows (rows bfTable r) [] = some (List.ofFn canonicalFixture.val)) :
    r = bfSchedule₁ :=
  schedule_eq_of_same_output bfTable bfTable r bfSchedule₁ canonicalFixture.val h
    rankFixture_success

-- 実際の内側置換が変化する二行でも、非退化成功の前行末は内側にある。
example : ∃ b : Fin 2, (1 : Fin 4) = BarrattEccles.insertedPosition 2 2 1 b := by
  exact permutationComposition_vertical_endpoint_inserted
    (1 : Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 2)) (Equiv.swap 0 1)
    1 [] [0, 1, 2, 1, 3] 1 2 3 [] (by decide) (by decide) (by decide)
-- 同じ成功の更新後の次行先頭も内側にある。
example : ∃ b : Fin 2, (2 : Fin 4) = BarrattEccles.insertedPosition 2 2 1 b := by
  exact permutationComposition_vertical_next_head_inserted
    (1 : Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 2)) (Equiv.swap 0 1)
    1 [] [0, 1, 2, 1, 3] 1 2 2 3 [] (by decide) (by decide) (by decide) (by decide)

-- 最終行直前までの二行を、実際の合成成功から元の内側抽出へ射影する。
private def reverseVerticalEntries : List (Equiv.Perm (Fin 2) × ℕ) :=
  [(1, 2), (Equiv.swap 0 1, 1)]
private lemma reverseVerticalPrefix :
    ExtractionPrefix (verticalTable (1 : Equiv.Perm (Fin 3)) 1 reverseVerticalEntries)
      [] [[0, 1], [2]] [0] := by
  have he : verticalTable (1 : Equiv.Perm (Fin 3)) 1 reverseVerticalEntries =
      [([0, 1, 2, 3], 2), ([0, 2, 1, 3], 1)] := by decide
  rw [he]
  exact .cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil _))
example : ExtractionPrefix ([([0, 1], 1), ([1, 0], 1)] : List (List (Fin 2) × ℕ))
    [] [[0], [1]] [] := by
  have hp := vertical_prefix_inner_projection (1 : Equiv.Perm (Fin 3)) 1
    reverseVerticalEntries (1 : Equiv.Perm (Fin 2)) 3 [] [] [0] [1, 2, 3] [[0, 1], [2]]
    reverseVerticalPrefix (by decide) (by decide)
  convert hp using 1 <;> decide

-- 外側文字で終わる最終行も内側末尾を残し、垂直成分全体を復元する。
example : ExtractionPrefix
    ([([0, 1], 1), ([1, 0], 1), ([0, 1], 2)] : List (List (Fin 2) × ℕ))
    [] [[0], [1], [0, 1]] [0] := by
  have hp := vertical_interval_inner_projection (1 : Equiv.Perm (Fin 3)) 1
    reverseVerticalEntries (1 : Equiv.Perm (Fin 2)) 3 [] [] [0] [1, 2, 3] [[0, 1], [2]]
    reverseVerticalPrefix (by decide) (by decide) (by decide)
  convert hp using 1 <;> decide
-- 同じ最終行の元の除外更新は内側選択語全体を除く。復元状態では末尾を残す。
example : (([1, 2, 3] : List (Fin 4)).take 2).filterMap
    (CompositeRecovery.innerLabel (m := 2) (n := 2) 1) =
    (([1, 2, 3] : List (Fin 4)).take 3).filterMap
      (CompositeRecovery.innerLabel (m := 2) (n := 2) 1) := by
  exact filterMap_selection_discarded_last (CompositeRecovery.innerLabel (m := 2) (n := 2) 1)
    [1, 2, 3] 3 (by decide) 3 (by decide) (by decide)

-- 内側文字が一つだけ除外されても、外側指定値はまだ可用である。
example : CompositeRecovery.outerRemoved (m := 2) (n := 2) 1 [1] = [] := by decide
-- 内側文字を全て除外した時点で、外側指定値も除外される。
example : CompositeRecovery.outerRemoved (m := 2) (n := 2) 1 [1, 2] = [1] := by decide
example : AdjacentCollapse.collapse
    ((available [1] (List.ofFn
      (BarrattEccles.permutationComposition 2 2 1 (1 : Equiv.Perm (Fin 3))
        (Equiv.swap 0 1)).symm)).map
        (CompositeRecovery.outerLabel (m := 2) (n := 2) 1)) = [0, 1, 2] := by
  exact (CompositeRecovery.outerLabel_available_composition_row 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 1) [1]).trans (by decide)
example : AdjacentCollapse.collapse
    ((available [1, 2] (List.ofFn
      (BarrattEccles.permutationComposition 2 2 1 (1 : Equiv.Perm (Fin 3))
        (Equiv.swap 0 1)).symm)).map
        (CompositeRecovery.outerLabel (m := 2) (n := 2) 1)) = [0, 2] := by
  exact (CompositeRecovery.outerLabel_available_composition_row 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 1) [1, 2]).trans (by decide)
-- 内側 arity 零では初期状態から指定値が消える。同じ一般定理を適用する。
example : CompositeRecovery.outerRemoved (m := 2) (n := 0) 1 [] = [1] := by decide
example : AdjacentCollapse.collapse
    ((available [] (List.ofFn
      (BarrattEccles.permutationComposition 2 0 1 (1 : Equiv.Perm (Fin 3))
        (1 : Equiv.Perm (Fin 0))).symm)).map
        (CompositeRecovery.outerLabel (m := 2) (n := 0) 1)) = [0, 2] := by
  exact (CompositeRecovery.outerLabel_available_composition_row 1
    (1 : Equiv.Perm (Fin 3)) (1 : Equiv.Perm (Fin 0)) []).trans (by decide)

-- 重複区間の途中で切った後続も、縮約後の対応順位へ戻る。
example : AdjacentCollapse.collapse (([0, 0, 1, 1, 0, 0] : List (Fin 2)).drop 3) =
    [1, 0] := by
  exact (AdjacentCollapse.collapse_drop_rank [0, 0, 1, 1, 0, 0] 3 (by decide)).trans
    (by decide)
private def outerRecoveryEntries :
    List (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) × ℕ) :=
  [(1, 1, 2), (1, Equiv.swap 0 1, 1), (1, 1, 3)]
private lemma outerRecoveryPrefix : ExtractionPrefix
    (CompositeRecovery.mixedTable 1 outerRecoveryEntries) [] [[0, 1], [2], [1, 2, 3]]
    [0, 1, 2] := by
  have he : CompositeRecovery.mixedTable 1 outerRecoveryEntries =
      [([0, 1, 2, 3], 2), ([0, 2, 1, 3], 1), ([0, 1, 2, 3], 3)] := by decide
  rw [he]
  exact .cons (by decide) (by decide)
    (.cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil _)))
-- 全合成抽出から復元した外側表は、垂直移動による同じ外側行をまだ保持する。
example : reduceRows
    ([([0, 1, 2], 2), ([0, 1, 2], 1), ([0, 1, 2], 2)] : List (List (Fin 3) × ℕ)) [] =
    some [0, 1, 1, 1, 2] := by
  have hp := CompositeRecovery.outer_prefix_success 1 outerRecoveryEntries [] [0, 1, 2]
    [[0, 1], [2], [1, 2, 3]] outerRecoveryPrefix [] [] rfl
  convert hp using 1 <;> decide

-- 外側の三重行を一行に融合し、共有文字は一度だけ数える。
example : compressRows
    ([([0, 1, 2], 2), ([0, 1, 2], 1), ([0, 1, 2], 2)] : List (List (Fin 3) × ℕ)) =
    [([0, 1, 2], 3)] := by decide
-- 離れた同じ行は融合しない。
example : (compressRows
    ([([0, 1], 1), ([1, 0], 1), ([0, 1], 1)] : List (List (Fin 2) × ℕ))).map Prod.fst =
    [[0, 1], [1, 0], [0, 1]] := by
  exact (compressRows_fst _).trans (by decide)
-- 実際の合成表から圧縮外側表と、その縮約出力の全体一致を得る。
example : ∃ picked finish out',
    ExtractionPrefix (CompositeRecovery.mixedTable 1 outerRecoveryEntries) [] picked finish ∧
      [0, 1, 2, 1, 2, 3] = picked.flatten ∧
      reduceRows (compressRows (CompositeRecovery.recoveredOuterTable 1
        outerRecoveryEntries picked)) [] = some out' ∧
      AdjacentCollapse.collapse out' = [0, 1, 2] := by
  have hs : reduceRows (CompositeRecovery.mixedTable 1 outerRecoveryEntries) [] =
      some [0, 1, 2, 1, 2, 3] := by
    simpa using outerRecoveryPrefix.append [] [] rfl
  obtain ⟨picked, finish, out', hp, ho, ht, hc⟩ :=
    CompositeRecovery.compressed_outer_table_success 1 outerRecoveryEntries [] _ hs
  refine ⟨picked, finish, out', hp, ho, ?_, hc.trans (by decide)⟩
  simpa only [CompositeRecovery.outerRemoved_nil (m := 2) (n := 2) 1 (by decide)] using ht

-- 前行末が内側、次行頭が外側の水平移動でも外側選択語の連結は非退化。
example : ([0, 1, 2, 1] : List (Fin 3)).IsChain (· ≠ ·) := by
  have hp := CompositeRecovery.horizontal_outer_selections_isChain 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 2) (1 : Equiv.Perm (Fin 2))
    [] [0, 1, 3, 1, 2] 2 3 [] (by decide) (by decide)
  convert hp using 1; decide
-- 前行末が外側、次行頭が内側の場合も同じ一般定理を使う。
example : ([0, 1, 0, 2] : List (Fin 3)).IsChain (· ≠ ·) := by
  have hp := CompositeRecovery.horizontal_outer_selections_isChain 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 1) (1 : Equiv.Perm (Fin 2))
    [] [0, 1, 2, 0, 3] 1 4 [] (by decide) (by decide)
  convert hp using 1; decide
-- 内側 arity 零も元の指定値を消した外側語の同じ境界定理に含む。
example : ([0, 2, 0] : List (Fin 3)).IsChain (· ≠ ·) := by
  have hp := CompositeRecovery.horizontal_outer_selections_isChain 1
    (1 : Equiv.Perm (Fin 3)) (Equiv.swap 0 2) (1 : Equiv.Perm (Fin 0))
    [] [0, 1, 0] 1 2 [] (by decide) (by decide)
  convert hp using 1; decide

-- 垂直・水平を交互に持つ実際の合成表から元の bfTable の Schedule まで戻す。
private def gridRecoveryEntries :
    List (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 2) × ℕ) :=
  [(1, 1, 2), (1, Equiv.swap 0 1, 1),
    (Equiv.swap 1 3, Equiv.swap 0 1, 1), (Equiv.swap 2 3, Equiv.swap 0 1, 4)]
private lemma gridRecoveryPrefix : ExtractionPrefix
    (CompositeRecovery.mixedTable 1 gridRecoveryEntries) []
    [[0, 1], [2], [4], [2, 1, 4, 3]] [0, 2, 1, 4] := by
  have he : CompositeRecovery.mixedTable 1 gridRecoveryEntries =
      [([0, 1, 2, 3, 4], 2), ([0, 2, 1, 3, 4], 1),
        ([0, 4, 3, 2, 1], 1), ([0, 2, 1, 4, 3], 4)] := by decide
  rw [he]
  exact .cons (by decide) (by decide) (.cons (by decide) (by decide)
    (.cons (by decide) (by decide) (.cons (by decide) (by decide) (.nil _))))
example : reduceRows (rows bfTable bfSchedule₁) [] = some [0, 1, 3, 1, 3, 2] := by
  have hsuccess : reduceRows (CompositeRecovery.mixedTable 1 gridRecoveryEntries) [] =
      some [0, 1, 2, 4, 2, 1, 4, 3] := by
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨picked, finish, hp, _, hs, _⟩ :=
    CompositeRecovery.compressed_outer_table_nondegenerate 1 gridRecoveryEntries [] _
      hsuccess (by decide) (by decide)
  obtain ⟨hwords, _⟩ := hp.unique gridRecoveryPrefix
  rw [hwords] at hs
  have htable : compressRows (CompositeRecovery.recoveredOuterTable 1 gridRecoveryEntries
      [[0, 1], [2], [4], [2, 1, 4, 3]]) = rows bfTable bfSchedule₁ := by decide
  rw [htable, CompositeRecovery.outerRemoved_nil (m := 3) (n := 2) 1 (by decide)] at hs
  convert hs using 1; decide

-- 同じ四行の例を実際の ShufflePath と Schedule から生成する。
private def gridRecoveryPath : BarrattEccles.ShufflePath 2 1 := ⟨{1, 2}, by decide⟩
private def gridRecoverySchedule : Schedule 5 3 := ⟨![2, 1, 1, 4], by decide⟩
example : AdjacentCollapse.collapse (List.ofFn (fun i =>
    (![0, 1, 0] : Fin 3 → Fin 2) (gridRecoveryPath.horizontal i))) = [0, 1, 0] := by
  exact (CompositeRecovery.collapse_horizontal_ofFn gridRecoveryPath _).trans (by decide)
example : ∃ table : List (List (Fin 4) × ℕ),
    reduceRows table [] = some [0, 1, 3, 1, 3, 2] ∧
      table.map Prod.fst = List.ofFn (fun j => List.ofFn (bfTable j).symm) ∧ table.length = 3 := by
  have hentries : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  have hsuccess : reduceRows (rows (fun i => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal i)) (terminalTable (gridRecoveryPath.vertical i)))
      gridRecoverySchedule) [] = some [0, 1, 2, 4, 2, 1, 4, 3] := by
    rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule, hentries]
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨picked, finish, _, _, hs, _, hrows, hlen⟩ :=
    CompositeRecovery.shuffle_outer_recovery_with_rows (by decide) 1 gridRecoveryPath
      bfTable terminalTable gridRecoverySchedule _ hsuccess (by decide)
  exact ⟨_, by convert hs using 1; decide, hrows, hlen⟩

-- 外側 Schedule を仮定せず実際の shuffle 成功から構成し、既知の Schedule との一致を証明する。
example : ∃ r : Schedule 4 2, r = bfSchedule₁ ∧
    reduceRows (rows bfTable r) [] = some (List.ofFn canonicalFixture.val) := by
  have hentries : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  have hsuccess : reduceRows (rows (fun i => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal i)) (terminalTable (gridRecoveryPath.vertical i)))
      gridRecoverySchedule) [] = some [0, 1, 2, 4, 2, 1, 4, 3] := by
    rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule, hentries]
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨r, hs, _, _⟩ := CompositeRecovery.shuffle_outer_schedule (by decide) 1
    gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ hsuccess (by decide)
  have hw : CompositeRecovery.outerWord (m := 3) (n := 2) 1
      [0, 1, 2, 4, 2, 1, 4, 3] = List.ofFn canonicalFixture.val := by decide
  rw [hw] at hs
  exact ⟨r, schedule_eq_of_same_output bfTable bfTable r bfSchedule₁
    canonicalFixture.val hs rankFixture_success, hs⟩

-- 全射性の補題は隣接重複のある成功出力にも適用できる。
example : ∀ a : Fin 2, a ∈ ([0, 0, 1] : List (Fin 2)) := by
  let r : Schedule 2 1 := ⟨![1, 2], by decide⟩
  apply output_covers (fun _ => (1 : Equiv.Perm (Fin 2))) r
  decide

private lemma innerIdentityInverseRow :
    List.ofFn (1 : Equiv.Perm (Fin 2)).symm = [0, 1] := by decide
-- 内側射影が空の先頭・末尾行と、全消費する中間行を同時に融合する。
private def innerHorizontalEntries : List (Equiv.Perm (Fin 3) × ℕ) :=
  [(1, 1), (Equiv.swap 0 1, 3), (Equiv.swap 0 2, 2)]
private lemma innerHorizontalPrefix : ExtractionPrefix
    (fixedInnerRows (1 : Equiv.Perm (Fin 2)) 1 innerHorizontalEntries) []
    [[0], [1, 2, 0], [3, 0]] [1, 2, 3] := by
  have he : fixedInnerRows (1 : Equiv.Perm (Fin 2)) 1 innerHorizontalEntries =
      [([0, 1, 2, 3], 1), ([1, 2, 0, 3], 3), ([3, 1, 2, 0], 2)] := by decide
  rw [he]
  exact .cons (by decide) (by decide) (.cons (by decide) (by decide)
    (.cons (by decide) (by decide) (.nil _)))
example : ∃ r : ℕ, reduceRows [([0, 1], r)] ([] : List (Fin 2)) = some [0, 1] := by
  obtain ⟨r, hr⟩ := horizontal_inner_success (1 : Equiv.Perm (Fin 2)) 1
    innerHorizontalEntries [] [1, 2, 3] [[0], [1, 2, 0], [3, 0]] innerHorizontalPrefix
    (by decide)
  rw [innerIdentityInverseRow, List.filterMap_nil] at hr
  exact ⟨r, by convert hr using 1; decide⟩
-- 元の末尾が外側でも、復元した内側末尾一文字は共有端点として残す。
example : ∃ r : ℕ, ExtractionPrefix [([0, 1], r)] ([] : List (Fin 2)) [[0, 1]] [0] := by
  obtain ⟨r, hr⟩ := horizontal_inner_close (1 : Equiv.Perm (Fin 2)) (m := 2) 1
    [] 1 4 [] [] [] (.nil _) (by decide)
  rw [innerIdentityInverseRow] at hr
  exact ⟨r, by convert hr using 1 <;> decide⟩
-- 水平一歩の後の垂直移動から、内側非空性と末尾保持を追加仮定なしで得る。
example : ∃ r : ℕ, ExtractionPrefix [([0, 1], r)] ([] : List (Fin 2)) [[0]] [] := by
  have hp : ExtractionPrefix (fixedInnerRows (1 : Equiv.Perm (Fin 2)) (m := 2) 1 [(1, 1)])
      [] [[0]] [] := by
    have he : fixedInnerRows (1 : Equiv.Perm (Fin 2)) (m := 2) 1 [(1, 1)] =
        [([0, 1, 2, 3], 1)] := by decide
    rw [he]
    exact .cons (by decide) (by decide) (.nil _)
  have ht : reduceRows
      [(List.ofFn (BarrattEccles.permutationComposition 2 2 1 (Equiv.swap 0 1) 1).symm, 1),
        (List.ofFn (BarrattEccles.permutationComposition 2 2 1 (Equiv.swap 0 1)
          (Equiv.swap 0 1)).symm, 4)] [] = some [1, 2, 1, 0, 3] := by decide
  obtain ⟨r, hr⟩ := horizontal_inner_before_vertical (1 : Equiv.Perm (Fin 2))
    (Equiv.swap 0 1) (m := 2) 1 [(1, 1)] (Equiv.swap 0 1) 1 4 [] [] _ [[0]] [] hp ht
    (by decide)
  rw [innerIdentityInverseRow] at hr
  exact ⟨r, by convert hr using 1 <;> decide⟩
-- 水平零歩も同じ規則に含み、次の垂直移動の前の実際の除外状態を保持する。
example : ∃ r : ℕ, ExtractionPrefix [([0, 1], r)] ([] : List (Fin 2)) [[0]] [] := by
  have ht : reduceRows
      [(List.ofFn (BarrattEccles.permutationComposition 2 2 1 1 1).symm, 2),
        (List.ofFn (BarrattEccles.permutationComposition 2 2 1 1 (Equiv.swap 0 1)).symm, 3)] [] =
      some [0, 1, 2, 1, 3] := by decide
  obtain ⟨r, hr⟩ := horizontal_inner_before_vertical (1 : Equiv.Perm (Fin 2))
    (Equiv.swap 0 1) (m := 2) 1 [] 1 2 3 [] [] _ [] [] (.nil _) ht (by decide)
  rw [innerIdentityInverseRow] at hr
  exact ⟨r, by convert hr using 1 <;> decide⟩

-- 実際の軸方向条件から全水平区間を分割し、元の内側置換列へ戻す。
example : CompositeRecovery.InnerRunDecomposition gridRecoveryEntries
    [1, Equiv.swap 0 1] := by
  obtain ⟨sources, hd⟩ := CompositeRecovery.innerRunDecomposition_exists
    (1 : Equiv.Perm (Fin 4)) (1 : Equiv.Perm (Fin 2)) 2 gridRecoveryEntries.tail (by decide)
  have hm := hd.sources_eq
  have he : (1 : Equiv.Perm (Fin 2)) :: sources = [1, Equiv.swap 0 1] :=
    hm.symm.trans (by decide)
  rw [he] at hd
  exact hd
-- 水平・垂直が交互に現れる合成成功から、元の全内側行列の成功を得る。
example : ∃ table : List (List (Fin 2) × ℕ),
    reduceRows table [] = some [0, 1, 0] ∧
      table.map Prod.fst = List.ofFn (fun j => List.ofFn (terminalTable j).symm) ∧
      table.length = 2 := by
  have hentries : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  have hs : reduceRows (rows (fun i => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal i)) (terminalTable (gridRecoveryPath.vertical i)))
      gridRecoverySchedule) [] = some [0, 1, 2, 4, 2, 1, 4, 3] := by
    rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule, hentries]
    simpa using gridRecoveryPrefix.append [] [] rfl
  obtain ⟨table, ht, _, hm, hl, _⟩ := CompositeRecovery.shuffle_inner_recovery_with_rows
    (by decide) 1 gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ hs (by decide)
  refine ⟨table, ?_, hm, hl⟩
  have hw : CompositeRecovery.innerWord (m := 3) (n := 2) 1
      [0, 1, 2, 4, 2, 1, 4, 3] = [0, 1, 0] := by decide
  rwa [hw] at ht
-- 内側次数零では、内側射影が空の最終行も全表に含めて元の一行を得る。
example : ∃ table : List (List (Fin 2) × ℕ),
    reduceRows table [] = some [0, 1] ∧ table.map Prod.fst = [[0, 1]] := by
  let entries : List (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 2) × ℕ) :=
    innerHorizontalEntries.map (fun p => (p.1, 1, p.2))
  have hs : reduceRows (CompositeRecovery.mixedTable 1 entries) [] =
      some [0, 1, 2, 0, 3, 0] := by
    rw [CompositeRecovery.mixedTable_horizontal]
    simpa using innerHorizontalPrefix.append [] [] rfl
  obtain ⟨table, hm, ht⟩ := CompositeRecovery.inner_table_success 1 entries [] _ hs
    (by decide) (by decide) (by decide)
  refine ⟨table, ?_, ?_⟩
  · have hw : CompositeRecovery.innerWord (m := 2) (n := 2) 1
        [0, 1, 2, 0, 3, 0] = [0, 1] := by decide
    simpa only [List.filterMap_nil, hw] using ht
  · exact hm.trans (by decide)

private lemma innerGrid_success : reduceRows (rows (fun i =>
    BarrattEccles.permutationComposition 3 2 1 (bfTable (gridRecoveryPath.horizontal i))
      (terminalTable (gridRecoveryPath.vertical i))) gridRecoverySchedule) [] =
    some [0, 1, 2, 4, 2, 1, 4, 3] := by
  have he : CompositeRecovery.shuffleTableEntries gridRecoveryPath bfTable terminalTable
      gridRecoverySchedule = gridRecoveryEntries := by decide
  rw [← CompositeRecovery.shuffleTableEntries_rows 1 gridRecoveryPath bfTable terminalTable
    gridRecoverySchedule, he]
  simpa using gridRecoveryPrefix.append [] [] rfl
private lemma innerGrid_word : CompositeRecovery.innerWord (m := 3) (n := 2) 1
    [0, 1, 2, 4, 2, 1, 4, 3] = List.ofFn compositionInner.val := by decide
-- 行長総和を仮定せず復元した内側 Schedule が既知の元の Schedule に一致する。
example : ∃ r : Schedule 2 1, r = terminalSchedule ∧
    reduceRows (rows terminalTable r) [] = some (List.ofFn compositionInner.val) := by
  obtain ⟨r, hs, _, _⟩ := CompositeRecovery.shuffle_inner_schedule (by decide) 1 gridRecoveryPath
    bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  rw [innerGrid_word] at hs
  exact ⟨r, schedule_eq_of_same_output terminalTable terminalTable r terminalSchedule
    compositionInner.val hs verticalInner_success, hs⟩
-- 内側基底語の元の次数と成功 Schedule の一意性も実際の shuffle 成功から得る。
example : ∃ v : BasisWord 2 1, v = compositionInner ∧
    ∃! r : Schedule 2 1, reduceRows (rows terminalTable r) [] = some (List.ofFn v.val) := by
  obtain ⟨v, hv, hr⟩ := CompositeRecovery.shuffle_inner_basis (by decide) 1 gridRecoveryPath
    bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  refine ⟨v, ?_, hr⟩
  apply Subtype.ext
  exact List.ofFn_injective (hv.trans innerGrid_word)
-- 内側次数零でも、内側を選ばない末尾行を含む全合成 Schedule から復元する。
example : ∃ r : Schedule 2 0,
    reduceRows (rows (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 2))) r) [] = some [0, 1] := by
  let s : BarrattEccles.ShufflePath 2 0 := ⟨{0, 1}, by decide⟩
  let outer : Fin 3 → Equiv.Perm (Fin 3) := ![1, Equiv.swap 0 1, Equiv.swap 0 2]
  let inner : Fin 1 → Equiv.Perm (Fin 2) := fun _ => 1
  let r : Schedule 4 2 := ⟨![1, 3, 2], by decide⟩
  have hs : reduceRows (rows (fun i => BarrattEccles.permutationComposition 2 2 1
      (outer (s.horizontal i)) (inner (s.vertical i))) r) [] =
      some [0, 1, 2, 0, 3, 0] := by decide
  obtain ⟨q, hq, _, _⟩ := CompositeRecovery.shuffle_inner_schedule (by decide) 1 s outer inner r
    _ hs (by decide)
  have hw : CompositeRecovery.innerWord (m := 2) (n := 2) 1 [0, 1, 2, 0, 3, 0] = [0, 1] := by decide
  exact ⟨q, by simpa only [hw] using hq⟩

-- 隣接重複だけの縮約損失を数え、離れた同値を含む部分語の全共有端点を導く。
example : ([[0, 1, 0], [0, 2], [2, 0]] : List (List (Fin 3))).IsChain
    (fun pre post => pre.getLast? = post.head?) := by
  exact AdjacentCollapse.shared_endpoints_of_saturated _ (by decide) (by decide) (by decide)
-- 同じ三部分語から既存の OverlapPartition の全 segment を実際に再構成する。
example : ∃! r : OverlapPartition 3 5,
    r.segments (![0, 1, 0, 2, 0] : Fin 5 → Fin 3) = [[0, 1, 0], [0, 2], [2, 0]] := by
  exact OverlapPartition.existsUnique_of_rows
    ([[0, 1, 0], [0, 2], [2, 0]] : List (List (Fin 3))) (by decide) (by decide)
    (![0, 1, 0, 2, 0] : Fin 5 → Fin 3) (by decide) (by decide)
-- 実際の交互 shuffle 出力から取り出した区間が、元の既知の分割を一意に復元する。
private def gridSplitParts : List (List (Fin 2)) :=
  CompositeRecovery.splitParts 1 (List.ofFn canonicalFixture.val) [0, 1, 2, 4, 2, 1, 4, 3]
private lemma gridSplitParts_value : gridSplitParts = [[0, 1], [1, 0]] := by decide
example : ∃ r : OverlapPartition 2 3, r = verticalCuts ∧
    r.segments compositionInner.val = gridSplitParts := by
  have hc : ∀ row ∈ gridSplitParts, row.IsChain (· ≠ ·) := by
    rw [gridSplitParts_value]
    decide
  have hn : ∀ row ∈ gridSplitParts, row ≠ [] := by rw [gridSplitParts_value]; decide
  have hv : List.ofFn compositionInner.val = AdjacentCollapse.collapse gridSplitParts.flatten :=
    by decide
  have hs : gridSplitParts.flatten.length + 1 = 3 + gridSplitParts.length := by decide
  have hp := OverlapPartition.existsUnique_of_rows gridSplitParts hc hn compositionInner.val hv hs
  have hl : gridSplitParts.length = 2 := by decide
  rw [hl] at hp
  obtain ⟨r, hr, hu⟩ := hp
  have hknown : verticalCuts.segments compositionInner.val = gridSplitParts := by decide
  exact ⟨r, (hu verticalCuts hknown).symm, hr⟩
-- 異なる境界の二語は一文字も失わず、飽和条件の必要性を検証する。
example : (AdjacentCollapse.collapse ([0, 1] ++ [2, 0] : List (Fin 3))).length = 4 := by
  have h := AdjacentCollapse.collapse_append_length ([0, 1] : List (Fin 3)) [2, 0]
    (by decide) (by decide) (by decide) (by decide)
  simpa using h

-- 共有端点を入力せず、一般の代入分解と復元両語長から実際の分割を一意に構成する。
example : ∃ p : OverlapPartition 2 3, p = verticalCuts ∧
    compositeWord canonicalFixture compositionInner 1 p = [0, 1, 2, 4, 2, 1, 4, 3] := by
  have ho : List.ofFn canonicalFixture.val = CompositeRecovery.outerWord (m := 3) (n := 2) 1
      [0, 1, 2, 4, 2, 1, 4, 3] := by decide
  obtain ⟨p, hp, hu⟩ := CompositeRecovery.recovered_partition_existsUnique canonicalFixture
    compositionInner 1 [0, 1, 2, 4, 2, 1, 4, 3] (by decide) (by decide) ho innerGrid_word.symm
  have hk : compositeWord canonicalFixture compositionInner 1 verticalCuts =
      [0, 1, 2, 4, 2, 1, 4, 3] := by decide
  exact ⟨p, (hu verticalCuts hk).symm, hp⟩
-- 実際の成功から元の両語・一意な分割・一意な両成功 Schedule を全て得る。
example : ∃ u : BasisWord 4 2, ∃ v : BasisWord 2 1,
    u = canonicalFixture ∧ v = compositionInner ∧
      (∃! p : OverlapPartition (occurrenceCount u.val 1) 3,
        compositeWord u v 1 p = [0, 1, 2, 4, 2, 1, 4, 3]) ∧
      (∃! su : Schedule 4 2, reduceRows (rows bfTable su) [] = some (List.ofFn u.val)) ∧
      (∃! sv : Schedule 2 1, reduceRows (rows terminalTable sv) [] = some (List.ofFn v.val)) := by
  obtain ⟨u, v, hp, hu, hv, hsu, hsv⟩ := CompositeRecovery.shuffle_source_partition (by decide) 1
    gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  have ho : CompositeRecovery.outerWord (m := 3) (n := 2) 1 [0, 1, 2, 4, 2, 1, 4, 3] =
      List.ofFn canonicalFixture.val := by decide
  refine ⟨u, v, ?_, ?_, hp, hsu, hsv⟩
  · exact Subtype.ext (List.ofFn_injective (hu.trans ho))
  · exact Subtype.ext (List.ofFn_injective (hv.trans innerGrid_word))
-- 部分語分解自体は内側 arity 零にも適用でき、指定値のない復元外側語へ戻る。
example : ([0, 1] : List (Fin 2)) = substitute (n := 0) 1 [0, 2] [] := by
  have hp := CompositeRecovery.splitParts_properties (m := 2) (n := 0) 1 [0, 1] (by decide)
  have ho : CompositeRecovery.outerWord (m := 2) (n := 0) 1 [0, 1] = [0, 2] := by decide
  rw [ho] at hp
  have hs : CompositeRecovery.splitParts (m := 2) (n := 0) 1 [0, 2] [0, 1] = [] := by decide
  rw [hs] at hp
  exact hp.2.2.2

-- 実際の選択行列の三境界から、垂直一歩・水平二歩を元の経路なしで検出する。
example : ∀ i : Fin 3, CompositeRecovery.BoundaryInserted (m := 3) (n := 2) 1
    [[0, 1], [2], [4], [2, 1, 4, 3]] i.val ↔ i = 0 := by
  have ht : ExtractionTrace (rows (fun j => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal j)) (terminalTable (gridRecoveryPath.vertical j)))
      gridRecoverySchedule) [] [[0, 1], [2], [4], [2, 1, 4, 3]] := by
    apply extractionTrace_of_lengths
    · simpa using innerGrid_success
    · decide
  intro i
  exact (CompositeRecovery.boundaryInserted_iff_notMem 1 gridRecoveryPath bfTable terminalTable
    gridRecoverySchedule _ ht (by decide) i).trans (by fin_cases i <;> decide)
-- 一般の経路一意性から、正方向で構成した経路が元の実際の経路へ戻る。
private lemma gridPath_roundtrip :
    compositionPath canonicalFixture compositionInner 1 verticalCuts = gridRecoveryPath := by
  exact fullCompositionFixture.compositionPath_eq_of_success gridRecoveryPath gridRecoverySchedule
    _ innerGrid_success (by decide) (by decide)
private lemma gridSchedule_roundtrip : fullCompositionFixture.fusedSchedule =
    gridRecoverySchedule := by
  exact fullCompositionFixture.fusedSchedule_eq_of_success gridRecoveryPath gridRecoverySchedule
    _ innerGrid_success (by decide)
-- 元の成功二表・分割・経路・Schedule を全て戻す入力データが一意に構成される。
example : ∃ c : TableCompositionData 3 2 2 1, c = fullCompositionFixture ∧
    compositionPath c.outerWord c.innerWord c.slot c.cuts = gridRecoveryPath ∧
      c.fusedSchedule = gridRecoverySchedule := by
  obtain ⟨c, hc, hu⟩ := CompositeRecovery.shuffle_reconstruction_existsUnique (by decide) 1
    gridRecoveryPath bfTable terminalTable gridRecoverySchedule _ innerGrid_success (by decide)
  have hk : fullCompositionFixture.outer = bfTable ∧ fullCompositionFixture.inner = terminalTable ∧
      fullCompositionFixture.slot = 1 ∧ compositionPath fullCompositionFixture.outerWord
        fullCompositionFixture.innerWord fullCompositionFixture.slot fullCompositionFixture.cuts =
          gridRecoveryPath ∧ fullCompositionFixture.fusedSchedule = gridRecoverySchedule ∧
      compositeWord fullCompositionFixture.outerWord fullCompositionFixture.innerWord
        fullCompositionFixture.slot fullCompositionFixture.cuts = [0, 1, 2, 4, 2, 1, 4, 3] :=
    ⟨rfl, rfl, rfl, gridPath_roundtrip, gridSchedule_roundtrip, by decide⟩
  exact ⟨c, (hu fullCompositionFixture hk).symm, hc.2.2.2.1, hc.2.2.2.2.1⟩

private def fullSuccessSource : CompositionSuccess.Source bfTable terminalTable (1 : Fin 4) :=
  ⟨fullCompositionFixture, rfl, rfl, rfl⟩
private def gridSuccessTarget : CompositionSuccess.Target bfTable terminalTable (1 : Fin 4) :=
  ⟨(gridRecoveryPath, gridRecoverySchedule), _, innerGrid_success, by decide⟩
-- 有限成功項全単射の正方向は実際の既知の混合経路・Schedule を返す。
private lemma successForward_grid : CompositionSuccess.forward (by decide) fullSuccessSource =
    gridSuccessTarget := by
  apply Subtype.ext
  exact Prod.ext gridPath_roundtrip gridSchedule_roundtrip
-- 選んだ逆写像も元の成功二表と分割へ厳密に戻る。
example : (CompositionSuccess.equiv (by decide) bfTable terminalTable (1 : Fin 4)).symm
    gridSuccessTarget = fullSuccessSource := by
  have he : (CompositionSuccess.equiv (by decide) bfTable terminalTable (1 : Fin 4))
      fullSuccessSource = gridSuccessTarget := successForward_grid
  have hh := congrArg (CompositionSuccess.equiv (by decide) bfTable terminalTable (1 : Fin 4)).symm he
  simpa only [Equiv.symm_apply_apply] using hh.symm
-- 正方向の項の一致には経路の符号も含む。
example : CompositionSuccess.signedTerm ℤ bfTable terminalTable (1 : Fin 4)
    gridSuccessTarget.val = CompositionSuccess.sourceTerm ℤ fullSuccessSource := by
  rw [← successForward_grid]
  exact CompositionSuccess.forward_term ℤ (by decide) fullSuccessSource
-- 退化出力となる別の実際の Schedule は全経路和に含めても零。
private def degenerateGridSchedule : Schedule 5 3 := ⟨![5, 1, 1, 1], by decide⟩
example : CompositionSuccess.signedTerm ℤ bfTable terminalTable (1 : Fin 4)
    (gridRecoveryPath, degenerateGridSchedule) = 0 := by
  apply CompositionSuccess.signedTerm_eq_zero_of_not_successful
  rintro ⟨out, ho, hc⟩
  have hz : reduceRows (rows (fun j => BarrattEccles.permutationComposition 3 2 1
      (bfTable (gridRecoveryPath.horizontal j)) (terminalTable (gridRecoveryPath.vertical j)))
      degenerateGridSchedule) [] = some [0, 1, 2, 3, 4, 4, 4, 4] := by decide
  have he : out = [0, 1, 2, 3, 4, 4, 4, 4] := Option.some.inj (ho.symm.trans hz)
  rw [he] at hc
  exact (by decide : ¬ ([0, 1, 2, 3, 4, 4, 4, 4] : List (Fin 5)).IsChain (· ≠ ·)) hc
-- 全経路・全 Schedule を含む和が元の全成功二表と分割の符号付き和に一致する。
example :
    letI := CompositionSuccess.sourceFintype (by decide) bfTable terminalTable (1 : Fin 4)
    (∑ s : BarrattEccles.ShufflePath 2 1, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 3 2 1 (bfTable (s.horizontal j))
        (terminalTable (s.vertical j)))) =
      ∑ c : CompositionSuccess.Source bfTable terminalTable (1 : Fin 4),
        CompositionSuccess.sourceTerm ℤ c :=
  CompositionSuccess.sum_onSequence_eq_source ℤ (by decide) bfTable terminalTable 1

private def outerSuccessfulWord : SuccessfulWord bfTable :=
  ⟨(bfSchedule₁, canonicalFixture), rankFixture_success⟩
private def innerSuccessfulWord : SuccessfulWord terminalTable :=
  ⟨(terminalSchedule, compositionInner), verticalInner_success⟩
-- 元の入力データを二列の実際の成功と分割へ、添字の移送を含めて分ける。
example : (CompositionSuccess.wordsEquiv (by decide) bfTable terminalTable (1 : Fin 4))
    fullSuccessSource = ⟨outerSuccessfulWord, innerSuccessfulWord, verticalCuts⟩ := rfl
-- 各元列の TR を、実際の成功基底語の有限和へ展開する。
example : onSequence ℤ bfTable =
    ∑ p : SuccessfulWord bfTable, basis ℤ 4 2 (ULift.up p.val.2) :=
  onSequence_eq_sum_successfulWords ℤ (by decide) bfTable
-- 混合する全 shuffle と全 Schedule の和が、元の二つの TR の実際の部分合成に一致する。
example :
    (∑ s : BarrattEccles.ShufflePath 2 1, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 3 2 1 (bfTable (s.horizontal j))
        (terminalTable (s.vertical j)))) =
      Surjection.partialComposition ℤ 3 2 2 1 1 (onSequence ℤ bfTable)
        (onSequence ℤ terminalTable) :=
  onSequence_partialComposition_of_pos ℤ (by decide) bfTable terminalTable 1
-- 一方の元列が退化している場合も一般公式に含まれ、全 shuffle 側が零へ戻る。
example :
    (∑ s : BarrattEccles.ShufflePath 1 0, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 1 2 0
        ((fun _ : Fin 2 => (1 : Equiv.Perm (Fin 2))) (s.horizontal j))
        ((fun _ : Fin 1 => (1 : Equiv.Perm (Fin 2))) (s.vertical j)))) = 0 := by
  let outer : Fin 2 → Equiv.Perm (Fin 2) := fun _ => 1
  let inner : Fin 1 → Equiv.Perm (Fin 2) := fun _ => 1
  have h := onSequence_partialComposition_of_pos ℤ (by decide) outer inner (0 : Fin 2)
  have ho : onSequence ℤ outer = 0 :=
    onSequence_eq_zero_of_adjacent_eq ℤ outer 0 1 (by decide) rfl
  rw [ho] at h
  simpa only [map_zero, LinearMap.zero_apply] using h

-- 生成元上の有限和の一致を、実際の正規化鎖の任意の元の双線形合成まで延長する。
example (x : (BarrattEccles.normalizedChains ℤ 4).X 2)
    (y : (BarrattEccles.normalizedChains ℤ 2).X 1) :
    normalizedMap ℤ 5 3 (BarrattEccles.shuffleBilinear ℤ 3 2 1 2 1 x y) =
      Surjection.partialComposition ℤ 3 2 2 1 1 (normalizedMap ℤ 4 2 x)
        (normalizedMap ℤ 2 1 y) :=
  normalizedMap_shuffleBilinear_of_pos ℤ (by decide) 1 x y

-- 零 arity の正の内側次数でも、全正規化鎖に対する合成保存が成立する。
example (x : (BarrattEccles.normalizedChains ℤ 4).X 2)
    (y : (BarrattEccles.normalizedChains ℤ 0).X 1) :
    normalizedMap ℤ 3 3 (BarrattEccles.shuffleBilinear ℤ 3 0 1 2 1 x y) =
      Surjection.partialComposition ℤ 3 0 2 1 1 (normalizedMap ℤ 4 2 x)
        (normalizedMap ℤ 0 1 y) :=
  normalizedMap_shuffleBilinear_nullary_succ ℤ 1 x y
-- 外側出力 arity も零になる境界を含め、実際の各 shuffle 項が零となる。
example (s : BarrattEccles.ShufflePath 2 1)
    (outer : Fin 3 → Equiv.Perm (Fin 1)) (inner : Fin 2 → Equiv.Perm (Fin 0)) :
    onSequence ℤ (fun j => BarrattEccles.permutationComposition 0 0 0
      (outer (s.horizontal j)) (inner (s.vertical j))) = 0 :=
  onSequence_shuffle_nullary_succ ℤ 0 2 0 0 outer inner s
-- 空語挿入は一出現だけを残し、二出現の場合は分割が存在せず零になる。
private def emptyNullaryWord : BasisWord 0 0 := permutationWord 1
example : eraseSlotWord (0 : Fin 4) (List.ofFn canonicalFixture.val) = [0, 2, 0, 2, 1] := by
  decide
example : compositionOnWords ℤ canonicalFixture emptyNullaryWord 0 =
    listGenerator ℤ (d := 2) [0, 2, 0, 2, 1] := by
  rw [compositionOnWords_nullary_of_count_eq_one ℤ _ _ _ (by decide)]
  rfl
example : compositionOnWords ℤ canonicalFixture emptyNullaryWord 1 = 0 :=
  compositionOnWords_nullary_of_count_ne_one ℤ _ _ _ (by decide)
-- 反転した実際の置換行でも、指定値削除は既存 BE の空語挿入に一致する。
example : List.ofFn
    (BarrattEccles.permutationComposition 2 0 1 rowOuter (1 : Equiv.Perm (Fin 0))).symm =
      [1, 0] := by
  rw [permutationComposition_inverse_row_nullary]
  decide
-- 早期除外した元の二行の成功と削除後の成功を、全抽出の公式で結ぶ。
example :
    reduceRows [([0, 1], 1), ([0, 1], 2)] ([] : List (Fin 2)) =
      (reduceRows [([0, 1, 2], 1), ([0, 1, 2], 2)] [0]).map
        (eraseSlotWord (0 : Fin 3)) := by
  have h := reduceRows_eraseSlotWord_of_mem (0 : Fin 3)
    [([0, 1, 2], 1), ([0, 1, 2], 2)] [0] (by decide)
  exact h
example : reduceRows [([0, 1], 1), ([0, 1], 2)] ([] : List (Fin 2)) =
    some [0, 0, 1] := by decide

-- 非退化の nullary 成功表から、一回だけ指定値を挿入する実際の逆構成。
private def nullaryOuter : Fin 2 → Equiv.Perm (Fin 3) := ![1, Equiv.swap 1 2]
example : reduceRows (rows (fun j => BarrattEccles.permutationComposition 2 0 0
    (nullaryOuter j) (1 : Equiv.Perm (Fin 0))) terminalSchedule) [] = some [0, 1, 0] := by
  decide
example : reduceRows (nullarySourceRows nullaryOuter terminalSchedule) [0] =
    some [1, 2, 1] := by decide
example : ∃ before chosen after pre post,
    nullarySourceRows nullaryOuter terminalSchedule = before ++ chosen :: after ∧
    (0 : Fin 3) ∉ pre ∧ 0 ∉ post ∧ [0, 1, 0] = eraseSlotWord 0 (pre ++ post) ∧
    reduceRows (before ++ (chosen.1, chosen.2 + 1) :: after) [] =
      some (pre ++ 0 :: post) :=
  nullary_success_extension nullaryOuter 1 0 terminalSchedule [0, 1, 0] (by decide)

-- 延長された行長は元の Schedule であり、削除後の非退化語へ戻る。
private def nullaryLiftSchedule : Schedule 3 1 := ⟨![2, 2], by decide⟩
private def nullaryLiftWord : BasisWord 3 1 := ⟨![0, 1, 2, 1], by decide⟩
private def nullaryLiftSuccess : SuccessfulWord nullaryOuter :=
  ⟨(nullaryLiftSchedule, nullaryLiftWord), by decide⟩
private def nullaryLiftSource : NullarySource nullaryOuter 0 :=
  ⟨nullaryLiftSuccess, by decide⟩
private def nullaryTargetSuccess : SuccessfulWord (fun j =>
    BarrattEccles.permutationComposition 2 0 0 (nullaryOuter j) 1) :=
  ⟨(terminalSchedule, compositionInner), by decide⟩
example : List.ofFn (nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource).val.2.val =
    [0, 1, 0] := by
  rw [nullaryForward_word]
  rfl
example : nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource =
    nullaryTargetSuccess := by
  apply successfulWord_eq_of_word_eq _ _ _
  rw [nullaryForward_word]
  rfl
-- 空語との部分合成が実際の目標基底元へ一致することも係数環 ℤ 上で検証。
example : compositionOnWords ℤ nullaryLiftWord emptyNullaryWord 0 =
    basis ℤ 2 1 (ULift.up compositionInner) := by
  have h := nullaryForward_term ℤ (by decide) nullaryOuter 1 0 nullaryLiftSource
  rw [show nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource =
    nullaryTargetSuccess by
      apply successfulWord_eq_of_word_eq _ _ _
      rw [nullaryForward_word]
      rfl] at h
  exact h
-- 各実際の成功基底語には、語の削除で元へ戻る一出現の成功基底語が存在する。
example : ∃ p : SuccessfulWord nullaryOuter, occurrenceCount p.val.2.val 0 = 1 ∧
    eraseSlotWord 0 (List.ofFn p.val.2.val) = [0, 1, 0] :=
  nullary_successfulWord_lift_exists nullaryOuter 1 0 nullaryTargetSuccess
example : Function.Surjective (nullaryForward (by decide) nullaryOuter 1 (0 : Fin 3)) :=
  nullaryForward_surjective (by decide) nullaryOuter 1 0

-- 空語合成の有限対応は全単射で、具体的な非自明な二行の成功項を往復する。
example : nullarySuccessEquiv (by decide) nullaryOuter 1 0 nullaryLiftSource =
    nullaryTargetSuccess := by
  change nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource = nullaryTargetSuccess
  apply successfulWord_eq_of_word_eq _ _ _
  rw [nullaryForward_word]
  rfl
example : (nullarySuccessEquiv (by decide) nullaryOuter 1 0).symm nullaryTargetSuccess =
    nullaryLiftSource := by
  apply (nullarySuccessEquiv (by decide) nullaryOuter 1 0).injective
  rw [Equiv.apply_symm_apply]
  symm
  change nullaryForward (by decide) nullaryOuter 1 0 nullaryLiftSource = nullaryTargetSuccess
  apply successfulWord_eq_of_word_eq _ _ _
  rw [nullaryForward_word]
  rfl
-- 元の全成功項の空語部分合成和が、実際の削除表の TR に一致する。
example : onSequence ℤ (fun j => BarrattEccles.permutationComposition 2 0 0
    (nullaryOuter j) (1 : Equiv.Perm (Fin 0))) =
      Surjection.partialComposition ℤ 2 0 1 0 0 (onSequence ℤ nullaryOuter)
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)) :=
  onSequence_nullary_composition_of_pos ℤ (by decide) nullaryOuter 1 0
-- 出力 arity 零・次数零の明示的な空語境界も一般公式に含まれる。
example : onSequence ℤ (fun j : Fin 1 => BarrattEccles.permutationComposition 0 0 0
    ((fun _ : Fin 1 => (1 : Equiv.Perm (Fin 1))) j) (1 : Equiv.Perm (Fin 0))) =
      Surjection.partialComposition ℤ 0 0 0 0 0
        (onSequence ℤ (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 1))))
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)) :=
  onSequence_nullary_composition_zero_output ℤ 0
    (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 1))) 1 0
-- 内側零次数の全 shuffle 和に、退化する元列も含める。
example :
    (∑ s : BarrattEccles.ShufflePath 2 0, (s.sign : ℤ) • onSequence ℤ (fun j =>
      BarrattEccles.permutationComposition 3 0 1 (bfTable (s.horizontal j))
        ((fun _ : Fin 1 => (1 : Equiv.Perm (Fin 0))) (s.vertical j)))) =
      Surjection.partialComposition ℤ 3 0 2 0 1 (onSequence ℤ bfTable)
        (onSequence ℤ (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 0)))) :=
  onSequence_partialComposition ℤ 1 bfTable
    (fun _ : Fin 1 => (1 : Equiv.Perm (Fin 0)))
-- 任意の可換環・全 arity・全次数で、実際の正規化鎖の双線形合成を保存する。
example (A : Type) [CommRing A] (m n d e : ℕ) (k : Fin (m + 1))
    (x : (BarrattEccles.normalizedChains A (m + 1)).X d)
    (y : (BarrattEccles.normalizedChains A n).X e) :
    normalizedMap A (m + n) (d + e) (BarrattEccles.shuffleBilinear A m n k d e x y) =
      Surjection.partialComposition A m n d e k (normalizedMap A (m + 1) d x)
        (normalizedMap A n e y) := normalizedMap_shuffleBilinear A k x y
example (x : (BarrattEccles.normalizedChains ℤ 1).X 2)
    (y : (BarrattEccles.normalizedChains ℤ 0).X 0) :
    normalizedMap ℤ 0 2 (BarrattEccles.shuffleBilinear ℤ 0 0 0 2 0 x y) =
      Surjection.partialComposition ℤ 0 0 2 0 0 (normalizedMap ℤ 1 2 x)
        (normalizedMap ℤ 0 0 y) := normalizedMap_shuffleBilinear ℤ 0 x y

-- 全射語の二つの正次数の合成の微分には、外側が奇次数の場合に負符号が付く。
example (x : degreeModule ℤ 3 1) (y : degreeModule ℤ 2 1) :
    differential ℤ 4 1 (Surjection.partialComposition ℤ 2 2 1 1 0 x y) =
      Surjection.partialComposition ℤ 2 2 0 1 0 (differential ℤ 3 0 x) y -
        Surjection.partialComposition ℤ 2 2 1 0 0 x (differential ℤ 2 0 y) := by
  have h := Surjection.partialComposition_d_positive ℤ 2 2 0 0 0 x y
  rw [show (-1 : ℤ) ^ (0 + 1) = -1 by decide, neg_one_zsmul] at h
  simpa only [Surjection.degreeTransport_refl, sub_eq_add_neg] using h
-- 空語挿入の場合も外側微分との可換性を保つ。
example (x : degreeModule ℤ 3 2) :
    differential ℤ 2 1 (Surjection.partialComposition ℤ 2 0 2 0 1 x
      (basis ℤ 0 0 (ULift.up emptyNullaryWord))) =
      Surjection.partialComposition ℤ 2 0 1 0 1 (differential ℤ 3 1 x)
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)) :=
  Surjection.partialComposition_d_rightZero ℤ 2 0 1 1 x _
-- 一文字単位と空語への左単位、正次数への右単位。
example : Surjection.unitElement ℤ = basis ℤ 1 0 (ULift.up (permutationWord 1)) := rfl
example : Surjection.degreeTransport ℤ 0 (Nat.zero_add 0)
    (Surjection.arityTransport ℤ (Nat.zero_add 0) 0
      (Surjection.partialComposition ℤ 0 0 0 0 0 (Surjection.unitElement ℤ)
        (basis ℤ 0 0 (ULift.up emptyNullaryWord)))) =
      basis ℤ 0 0 (ULift.up emptyNullaryWord) :=
  Surjection.partialComposition_left_unit ℤ 0 0 _
example : Surjection.partialComposition ℤ 2 1 1 0 2
    (basis ℤ 3 1 (ULift.up compositionOuter)) (Surjection.unitElement ℤ) =
      basis ℤ 3 1 (ULift.up compositionOuter) :=
  Surjection.partialComposition_right_unit ℤ 2 2 1 _
-- 交換する二つの内側演算がともに奇次数なら並列交換の符号は負。
example (x : degreeModule ℤ 3 1) (y z : degreeModule ℤ 2 1) :
    Surjection.partialComposition ℤ 3 2 2 1 (BarrattEccles.parallelSlot 1 2 0 2 (by decide))
      (Surjection.partialComposition ℤ 2 2 1 1 0 x y) z =
      -Surjection.partialComposition ℤ 3 2 2 1
        (BarrattEccles.parallelSlot 1 2 2 0 (by decide))
        (Surjection.partialComposition ℤ 2 2 1 1 2 x z) y := by
  have h := Surjection.partialComposition_parallel_assoc ℤ 1 2 2 0 2 (by decide) 1 1 1 x y z
  rw [show (-1 : ℤ) ^ (1 * 1) = -1 by decide, neg_one_zsmul] at h
  simpa only [Surjection.degreeTransport_refl, Surjection.arityTransport_refl] using h
-- 整数複体の対称列と、その全射 TR の成分を検証する。
example : SerrePositivity.SymmetricSequence.level (Surjection.sequence ℤ) 2 = Surjection.complex ℤ 2 := rfl
example : (TableReduction.sequenceMap ℤ).app (SerrePositivity.FiniteBijection.of 2) = cochainMap ℤ 2 := rfl
example : Function.Surjective ((cochainMap ℤ 2).f (-2)).hom := cochainMap_f_surjective ℤ 2 2

open CategoryTheory CategoryTheory.MonoidalCategory

-- 非自明な二つの負次数の純粋テンソルで、整数部分合成は元の全射語合成になる。
open SerrePositivity.DifferentialGraded HomologicalComplex in
example (x : (Surjection.complex ℤ 3).X (-1)) (y : (Surjection.complex ℤ 2).X (-1)) :
    (Surjection.complexPartialComposition ℤ 2 2 0).f (-2)
        (ιTensorObj (Surjection.complex ℤ 3) (Surjection.complex ℤ 2) (-1) (-1) (-2)
          (by decide) (x ⊗ₜ[ℤ] y)) =
      (Surjection.complexXIso ℤ 4 2).inv
        (Surjection.partialComposition ℤ 2 2 1 1 0
          ((Surjection.complexXIso ℤ 3 1).hom x) ((Surjection.complexXIso ℤ 2 1).hom y)) :=
  Surjection.complexPartialComposition_neg_tmul ℤ 2 2 0 1 1 x y
-- 空語を含む実際の整数複体の射の合成保存。
example : BarrattEccles.partialComposition ℤ 2 0 1 ≫ cochainMap ℤ 2 =
    (cochainMap ℤ 3 ⊗ₘ cochainMap ℤ 0) ≫ Surjection.complexPartialComposition ℤ 2 0 1 :=
  complexPartialComposition_comm ℤ 2 0 1
-- 正次数の零成分も含めて整数 TR の全射性とテンソル消去が使える。
example : Function.Surjective ((cochainMap ℤ 0).f 1).hom := cochainMap_f_surjective_int ℤ 0 1
example : Epi (cochainMap ℤ 2 ⊗ₘ cochainMap ℤ 0) := tensor_cochainMap_epi ℤ 2 0
-- 複体射の単位の保存と、全整数次数を同時に扱う右単位則。
example : BarrattEccles.unit ℤ ≫ cochainMap ℤ 1 = Surjection.complexUnit ℤ := rfl
example : (Surjection.complex ℤ 3 ◁ Surjection.complexUnit ℤ) ≫
    Surjection.complexPartialComposition ℤ 2 1 2 = (ρ_ (Surjection.complex ℤ 3)).hom :=
  Surjection.complexPartialComposition_right_unit ℤ 2 2
-- 内側の非自明な置換も複体射の段階で同変。
example : (Surjection.complex ℤ 3 ◁ Surjection.complexRename ℤ 2 (Equiv.swap 0 1)⁻¹) ≫
    Surjection.complexPartialComposition ℤ 2 2 0 =
      Surjection.complexPartialComposition ℤ 2 2 0 ≫
        Surjection.complexRename ℤ 4
          (operadInnerPermutation 2 2 0 (Equiv.swap 0 1))⁻¹ :=
  Surjection.complexPartialComposition_inner_rightAction ℤ 2 2 0 (Equiv.swap 0 1)

-- 束ねた TR オペラッド射は nullary の代入にも構成済みの合成保存を使う。
example : BarrattEccles.partialComposition ℤ 2 0 1 ≫
    (TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 2) =
      ((TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 3) ⊗ₘ
        (TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 0)) ≫
          (Surjection.operad ℤ).comp 2 0 1 :=
  (TableReduction.operadMap ℤ).comp 2 0 1
-- 出力 arity 零の負次数と正次数の零成分も、同じオペラッド射の全射性が扱う。
example : Function.Surjective
    (((TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 0)).f (-2)).hom :=
  TableReduction.operadMap_f_surjective ℤ 0 (-2)
example : Function.Surjective
    (((TableReduction.operadMap ℤ).map.app (SerrePositivity.FiniteBijection.of 0)).f 1).hom :=
  TableReduction.operadMap_f_surjective ℤ 0 1

open SerrePositivity.EInfinity.IntervalCuts

-- 010 の唯一の非退化な辺の切断は、正符号の辺⊗辺を与える。
example : edgeValue ℤ compositionInner =
    Finsupp.single (fun _ : Fin 2 => IntervalCuts.edge) 1 := by
  have h0 : ¬ EdgeNondegenerate compositionInner.val 0 := by decide
  have h1 : EdgeNondegenerate compositionInner.val 1 := by decide
  have h2 : ¬ EdgeNondegenerate compositionInner.val 2 := by decide
  have hs : edgeSign compositionInner.val 1 = 1 := by decide
  have ho : edgeOutput compositionInner 1 = (fun _ : Fin 2 => IntervalCuts.edge) := by
    funext k
    fin_cases k <;> apply Subtype.ext <;> decide
  change (∑ p : Fin 3, edgeTerm ℤ compositionInner p) = _
  rw [Fin.sum_univ_three]
  simp [edgeTerm, h0, h1, h2, hs, ho]
-- 色を逆にした 101 では、同じ辺⊗辺の切断の符号が負になる。
example : edgeSign (![1, 0, 1] : Fin 3 → Fin 2) 1 = -1 := by decide
-- 頂点への正次数作用は退化し、辺の非零項の総次数は語次数+1。
example : vertexValue ℤ compositionInner 0 = 0 := rfl
example : ∑ k : Fin 2, simplexDegree (edgeOutput compositionInner 1 k) = 2 :=
  edgeOutput_total_degree compositionInner 1 (by decide)
-- arity 二の標準 AW の二つの切断は辺⊗一と零⊗辺。
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 0 0 = IntervalCuts.edge := by
  apply Subtype.ext
  decide
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 0 1 = IntervalCuts.vertex 1 := by
  apply Subtype.ext
  decide
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 1 0 = IntervalCuts.vertex 0 := by
  apply Subtype.ext
  decide
example : edgeOutput (permutationWord (1 : Equiv.Perm (Fin 2))) 1 1 = IntervalCuts.edge := by
  apply Subtype.ext
  decide

-- 同じ 010 の切断が、実際の N_*(Δ¹) の反復テンソルの次数 −2 に入る。
example : edgeComponent ℤ 2 1 (basis ℤ 2 1 (ULift.up compositionInner)) =
    tensorVectorOfDegree ℤ 2 2 (fun _ : Fin 2 => IntervalCuts.edge) (by decide) := by
  rw [edgeComponent_basis]
  have h0 : ¬ EdgeNondegenerate compositionInner.val 0 := by decide
  have h1 : EdgeNondegenerate compositionInner.val 1 := by decide
  have h2 : ¬ EdgeNondegenerate compositionInner.val 2 := by decide
  have hs : edgeSign compositionInner.val 1 = 1 := by decide
  have ho : edgeOutput compositionInner 1 = (fun _ : Fin 2 => IntervalCuts.edge) := by
    funext k
    fin_cases k <;> apply Subtype.ext <;> decide
  simp [edgeComponentOnWord, Fin.sum_univ_three, h0, h1, h2, hs, ho]
-- 実際の正規化区間の高次は退化によって零になる。
example : CategoryTheory.Limits.IsZero ((intervalChains ℤ).X 2) :=
  intervalChains_isZero ℤ 2 (by decide)
example : CategoryTheory.Limits.IsZero ((IntervalCuts.interval ℤ).X 1) :=
  interval_isZero_positive ℤ 1 (by decide)
-- 頂点への正次数の実際の成分も零。
example : vertexComponent ℤ 2 1 1 (basis ℤ 2 1 (ULift.up compositionInner)) = 0 := by
  rw [vertexComponent_basis]
  exact vertexComponentOnWord_eq_zero_of_positive ℤ compositionInner (by decide) 1

-- 二つの辺の後の因子を微分する境界項には負符号が付く。
open HomologicalComplex in
example : tensorBoundaryTerm ℤ 2 (fun _ => IntervalCuts.edge) 1 =
    -ιTensorObj (IntervalCuts.interval ℤ)
      (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 1) (-1) 0 (-1) (by decide)
      (faceVector ℤ IntervalCuts.edge ⊗ₜ[ℤ]
        tensorBoundaryTerm ℤ 1 (fun _ => IntervalCuts.edge) 0) := by
  change (-1 : ℤ).negOnePow •
    ιTensorObj (IntervalCuts.interval ℤ)
      (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 1) (-1) 0 (-1) _
      (faceVector ℤ IntervalCuts.edge ⊗ₜ[ℤ]
        tensorBoundaryTerm ℤ 1 (fun _ => IntervalCuts.edge) 0) = _
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.smul_def,
    Units.val_neg, Units.val_one, neg_one_zsmul]
-- 同じ頂点である必要はなく、任意の三つの端点のテンソルは実際に閉じている。
example (b : Fin 3 → Fin 2) :
    (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d 0 1
      (tensorVectorOfDegree ℤ 3 0 (fun i => IntervalCuts.vertex (b i))
        (by rw [tupleDegree_eq_sum]; simp)) = 0 :=
  tensorVectorOfDegree_d_eq_zero ℤ 3 0 _ _ (tensorVector_d_eq_zero_of_vertices ℤ 3 b)

-- 010 の左右の反復文字の削除は、それぞれ実際の語 10 と 01 を返す。
private def cutEraseLeft : BasisWord 2 0 :=
  eraseCutBasisWord compositionInner 1 0 (by decide) (by decide) ⟨2, by decide⟩
private def cutEraseRight : BasisWord 2 0 :=
  eraseCutBasisWord compositionInner 1 2 (by decide) (by decide) ⟨0, by decide⟩
example : cutEraseLeft.val = ![1, 0] := by funext i; fin_cases i <;> rfl
example : cutEraseRight.val = ![0, 1] := by funext i; fin_cases i <;> rfl
-- 残した切断点での全出力族は、元の辺を終点・始点へ置換したもの。
example : edgeOutput cutEraseLeft 0 =
    Function.update (edgeOutput compositionInner 1) 0 (IntervalCuts.vertex 1) :=
  edgeOutput_eraseCut_left compositionInner 0 0 (by decide) (by decide) ⟨2, by decide⟩
example : edgeOutput cutEraseRight 1 =
    Function.update (edgeOutput compositionInner 1) 0 (IntervalCuts.vertex 0) :=
  edgeOutput_eraseCut_right compositionInner 2 1 (by decide) (by decide) ⟨0, by decide⟩
-- 0102 の切断では第三の色は頂点なので、実際の境界和は二つの活動位置だけ。
example :
    (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d
        (-(tupleDegree 3 (edgeOutput compositionOuter 1) : ℤ))
        (-(tupleDegree 3 (edgeOutput compositionOuter 1) : ℤ) + 1)
        (tensorVector ℤ 3 (edgeOutput compositionOuter 1)) =
      tensorBoundaryTerm ℤ 3 (edgeOutput compositionOuter 1) 0 +
        tensorBoundaryTerm ℤ 3 (edgeOutput compositionOuter 1) 1 := by
  have hs : activePositions compositionOuter.val 1 = {0, 1} := by decide
  simpa only [hs, Finset.sum_pair (by decide : (0 : Fin 4) ≠ (1 : Fin 4))]
    using! edgeOutput_tensorVector_d ℤ compositionOuter 1 (by decide)

-- 三つの活動色 2,0,1 を持つ語。最初の色0の削除係数と残りの交換符号はともに負。
private def cutSignWord : BasisWord 3 2 := ⟨![2, 0, 1, 2, 0], by decide⟩
example : deletionCoefficient cutSignWord.val 1 = -1 ∧
    edgeSign (erase cutSignWord.val 1) 1 = -1 := by decide
-- 左出現の削除は、元の実際の切断と削除語の実際の切断の係数を保つ。
example : edgeSign cutSignWord.val 2 =
    deletionCoefficient cutSignWord.val 1 * edgeSign (erase cutSignWord.val 1) 1 := by
  have h := edgeSign_erase_left_boundary cutSignWord 1 1 (by decide) (by decide)
  rw [show (1 : Fin 5).succAbove (1 : Fin 4) = 2 by decide] at h
  have hp : (∑ k ∈ Finset.univ.filter (fun k : Fin 3 => k < cutSignWord.val 1),
      simplexDegree (edgeOutput cutSignWord 2 k)) = 0 := by decide
  simpa only [hp, pow_zero, mul_one] using h
-- 同じ色の右出現を削除する場合は、始点側の負の境界係数になる。
example : -edgeSign cutSignWord.val 2 =
    deletionCoefficient cutSignWord.val 4 * edgeSign (erase cutSignWord.val 4) 2 := by
  have h := edgeSign_erase_right_boundary cutSignWord 4 1 2
    (by decide) (by decide) (by decide)
  rw [show (4 : Fin 5).succAbove (2 : Fin 4) = 2 by decide] at h
  have hp : (∑ k ∈ Finset.univ.filter (fun k : Fin 3 => k < cutSignWord.val 1),
      simplexDegree (edgeOutput cutSignWord 2 k)) = 0 := by decide
  simpa only [hp, pow_zero, mul_one] using h

-- 010 の辺を端点に置換した実際のテンソルが、削除語の切断テンソルになる。
example : endpointTensor ℤ 2 (edgeOutput compositionInner 1) 0 (by decide) 1 =
    tensorVectorAt ℤ 2 (edgeOutput cutEraseLeft 0) (-1) (by decide) := by
  simpa only [show (0 : Fin 3).succAbove (0 : Fin 2) = 1 by decide]
    using! endpointTensor_eraseCut_left ℤ compositionInner 0 0
      (by decide) (by decide) ⟨2, by decide⟩
example : endpointTensor ℤ 2 (edgeOutput compositionInner 1) 0 (by decide) 0 =
    tensorVectorAt ℤ 2 (edgeOutput cutEraseRight 1) (-1) (by decide) := by
  simpa only [show (2 : Fin 3).succAbove (1 : Fin 2) = 1 by decide]
    using! endpointTensor_eraseCut_right ℤ compositionInner 2 1
      (by decide) (by decide) ⟨0, by decide⟩
-- 三つの辺の真ん中の色を微分すると、奇数の前方次数で終点側が負になる。
private def factorSignWord : BasisWord 3 2 := ⟨![1, 2, 0, 1, 2], by decide⟩
example : tensorBoundaryTerm ℤ 3 (edgeOutput factorSignWord 2) 1 =
    -endpointTensor ℤ 3 (edgeOutput factorSignWord 2) 1 (by decide) 1 +
      endpointTensor ℤ 3 (edgeOutput factorSignWord 2) 1 (by decide) 0 := by
  have h := cut_factor_boundary ℤ factorSignWord 0 3 1 2
    (by decide) (by decide) (by decide) (by decide)
  have hp : (0 : Fin 5).succAbove (1 : Fin 4) = 2 := by decide
  have hs : edgeSign factorSignWord.val 2 = 1 := by decide
  have hL : deletionCoefficient factorSignWord.val 0 *
      edgeSign (erase factorSignWord.val 0) 1 = -1 := by decide
  have hR : deletionCoefficient factorSignWord.val 3 *
      edgeSign (erase factorSignWord.val 3) 2 = 1 := by decide
  simpa only [hp, hs, hL, hR, one_smul, neg_one_zsmul] using! h

-- 01020 の最初の0を削除すると非零だが、元の切断は左側の重複で退化する。
private def residualWord : BasisWord 3 2 := ⟨![0, 1, 0, 2, 0], by decide⟩
private def residualFixture : NonpivotResidualCut residualWord.val where
  deleted := 0
  pivot := 2
  defect := 2
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : ¬ EdgeNondegenerate residualWord.val 3 := by decide
-- 交換相手は中央の0の削除で、同じ元切断点に戻る。二回交換すると厳密に元へ戻る。
example : residualFixture.swap.pivot = 2 := by
  apply (Fin.succAbove_right_injective (p := (2 : Fin 5)))
  exact residualFixture.partnerPosition_spec.1
example : residualFixture.swap.swap = residualFixture := residualFixture.swap_swap
example : residualFixture.swap ≠ residualFixture := residualFixture.swap_ne
example : (residualCutBasisWord residualWord residualFixture).val = ![1, 0, 2, 0] := by
  funext i
  fin_cases i <;> rfl
example : (residualCutBasisWord residualWord residualFixture.swap).val = ![0, 1, 2, 0] := by
  funext i
  fin_cases i <;> rfl
-- この相殺対の削除係数と切断符号の積は互いに反対。
example : deletionCoefficient residualWord.val 0 * edgeSign (erase residualWord.val 0) 2 =
    -(deletionCoefficient residualWord.val 2 * edgeSign (erase residualWord.val 2) 2) := by decide
-- 語は異なっても、実際の正規化区間テンソルでの切断値は同じ。
example :
    tensorVectorOfDegree ℤ 3 2 (edgeOutput (residualCutBasisWord residualWord residualFixture) 2)
        (edgeOutput_tupleDegree _ _ residualFixture.nondegenerate) =
      tensorVectorOfDegree ℤ 3 2
        (edgeOutput (residualCutBasisWord residualWord residualFixture.swap)
          residualFixture.swap.pivot)
        (edgeOutput_tupleDegree _ _ residualFixture.swap.nondegenerate) :=
  residualCut_tensor_eq ℤ residualWord residualFixture

-- 010210 は二つの区切りの削除係数が同じでも、切断符号が反転する三出現例。
private def residualTripleWord : BasisWord 3 3 := ⟨![0, 1, 0, 2, 1, 0], by decide⟩
private def residualTripleFixture : NonpivotResidualCut residualTripleWord.val where
  deleted := 0
  pivot := 2
  defect := 2
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : deletionCoefficient residualTripleWord.val 0 = 1 ∧
    deletionCoefficient residualTripleWord.val 2 = 1 ∧
    edgeSign (erase residualTripleWord.val 0) 2 = -1 ∧
    edgeSign (erase residualTripleWord.val 2) 2 = 1 := by decide
example : deletionCoefficient residualTripleWord.val residualTripleFixture.deleted *
      edgeSign (erase residualTripleWord.val residualTripleFixture.deleted)
        residualTripleFixture.pivot =
    -(deletionCoefficient residualTripleWord.val residualTripleFixture.swap.deleted *
      edgeSign (erase residualTripleWord.val residualTripleFixture.swap.deleted)
        residualTripleFixture.swap.pivot) := residualTripleFixture.swap_coefficient

-- 左側の最終出現との交換。切断符号は等しく、削除係数が反対になる。
private def residualFinalWord : BasisWord 3 2 := ⟨![0, 1, 0, 2, 1], by decide⟩
private def residualFinalFixture : NonpivotResidualCut residualFinalWord.val where
  deleted := 0
  pivot := 2
  defect := 2
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : ¬ Caesura residualFinalWord.val 2 := by decide
example : deletionCoefficient residualFinalWord.val residualFinalFixture.deleted *
      edgeSign (erase residualFinalWord.val residualFinalFixture.deleted)
        residualFinalFixture.pivot =
    -(deletionCoefficient residualFinalWord.val residualFinalFixture.swap.deleted *
      edgeSign (erase residualFinalWord.val residualFinalFixture.swap.deleted)
        residualFinalFixture.swap.pivot) := residualFinalFixture.swap_coefficient

-- 同じ最終出現交換の右側版と、その逆順も一般定理から得る。
private def residualRightFixture : NonpivotResidualCut residualWord.val where
  deleted := 2
  pivot := 1
  defect := 4
  nondegenerate := by decide
  defect_spec := by decide
  defect_ne_pivot := by decide
example : deletionCoefficient residualWord.val residualRightFixture.deleted *
      edgeSign (erase residualWord.val residualRightFixture.deleted) residualRightFixture.pivot =
    -(deletionCoefficient residualWord.val residualRightFixture.swap.deleted *
      edgeSign (erase residualWord.val residualRightFixture.swap.deleted)
        residualRightFixture.swap.pivot) := residualRightFixture.swap_coefficient
example : deletionCoefficient residualWord.val residualRightFixture.swap.deleted *
      edgeSign (erase residualWord.val residualRightFixture.swap.deleted)
        residualRightFixture.swap.pivot =
    -(deletionCoefficient residualWord.val residualRightFixture.deleted *
      edgeSign (erase residualWord.val residualRightFixture.deleted) residualRightFixture.pivot) := by
  simpa only [NonpivotResidualCut.swap_swap] using residualRightFixture.swap.swap_coefficient

-- 全添字の和も実際の ℤ 上の区間テンソルで零となる。
example : ∑ c : NonpivotResidualCut residualTripleWord.val,
    (deletionCoefficient residualTripleWord.val c.deleted *
      edgeSign (erase residualTripleWord.val c.deleted) c.pivot) •
      tensorVectorOfDegree ℤ 3 3 (edgeOutput (residualCutBasisWord residualTripleWord c) c.pivot)
        (edgeOutput_tupleDegree _ _ c.nondegenerate) = 0 :=
  residualCut_tensor_sum_eq_zero ℤ residualTripleWord

-- 01203 の非零切断は隣接する1,2の二つ。内部の端点置換は同じ隙間値。
private def pivotIntervalWord : BasisWord 4 1 := ⟨![0, 1, 2, 0, 3], by decide⟩
example : Function.update (edgeOutput pivotIntervalWord 1) 1 (IntervalCuts.vertex 0) =
    Function.update (edgeOutput pivotIntervalWord 2) 2 (IntervalCuts.vertex 1) := by
  rw [show (1 : Fin 4) = pivotIntervalWord.val 1 by rfl,
    show (2 : Fin 4) = pivotIntervalWord.val 2 by rfl,
    edgeOutput_pivot_endpoint_zero pivotIntervalWord 1 (by decide),
    edgeOutput_pivot_endpoint_one pivotIntervalWord 2 (by decide)]
  rfl
-- 共通係数は負で、実際の全因子境界和では内部項が消え、二端点だけが残る。
example : ∑ p, pivotBoundaryValue ℤ pivotIntervalWord p =
    -(gapTensor ℤ pivotIntervalWord 1 - gapTensor ℤ pivotIntervalWord 3) := by
  have h := pivotBoundaryValue_sum_of_endpoints ℤ pivotIntervalWord 1 2
    (by decide) (by decide) (by decide)
  have hs : (-1 : ℤ) ^ (Finset.univ.filter (Caesura pivotIntervalWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount pivotIntervalWord.val
        (Finset.univ.filter (Caesura pivotIntervalWord.val)) = -1 := by decide
  simpa only [hs, neg_one_zsmul] using! h
-- 同色三出現の語には非零切断がなく、全和も実際に零。
example : ∑ p, pivotBoundaryValue ℤ residualWord p = 0 := by
  have hs : ¬ (Finset.univ.filter (EdgeNondegenerate residualWord.val)).Nonempty := by decide
  simpa only [dite_eq_right hs] using! pivotBoundaryValue_sum ℤ residualWord
-- 次数零では全 arity・全置換語について入力辺の境界へ一致する。
example {n : ℕ} (u : BasisWord n 0) : ∑ p, pivotBoundaryValue ℤ u p =
    tensorVectorOfDegree ℤ n 0 (fun _ => IntervalCuts.vertex 1) (vertex_tupleDegree n 1) -
      tensorVectorOfDegree ℤ n 0 (fun _ => IntervalCuts.vertex 0) (vertex_tupleDegree n 0) :=
  pivotBoundaryValue_sum_zeroDegree ℤ u

-- 01202 の元の辺切断は全て退化するが、隙間3は非退化。
private def gapOnlyWord : BasisWord 3 2 := ⟨![0, 1, 2, 0, 2], by decide⟩
example : ∀ p, ¬ EdgeNondegenerate gapOnlyWord.val p := by decide
example : GapNondegenerate gapOnlyWord.val 3 := by decide
-- 隙間の右隣3には左の0、左隣2には右の2が一意な削除相手となる。
example : ∃! i, i < (3 : Fin 5) ∧ gapOnlyWord.val i = gapOnlyWord.val 3 :=
  gap_before_defect_existsUnique gapOnlyWord.val 3 (by decide) (by decide)
example : ∃! i, (2 : Fin 5) < i ∧ gapOnlyWord.val i = gapOnlyWord.val 2 :=
  gap_after_defect_existsUnique gapOnlyWord.val 2 (by decide) (by decide)
example : EdgeNondegenerate (erase gapOnlyWord.val 0) 2 :=
  erase_edgeNondegenerate_of_gap_before gapOnlyWord.val 0 2
    (by decide) (by decide) (by decide)
example : EdgeNondegenerate (erase gapOnlyWord.val 4) 2 :=
  erase_edgeNondegenerate_of_gap_after gapOnlyWord.val 4 2
    (by decide) (by decide) (by decide)
-- 二つの異なる実際の削除語は、それぞれ同じ隙間3のテンソル値へ戻る。
private def gapOnlyLeft : BasisWord 3 1 :=
  pivotEraseBasisWord gapOnlyWord 0 2 (by decide) (by decide)
private def gapOnlyRight : BasisWord 3 1 :=
  pivotEraseBasisWord gapOnlyWord 4 2 (by decide) (by decide)
example : gapOnlyLeft.val = ![1, 2, 0, 2] := by funext i; fin_cases i <;> rfl
example : gapOnlyRight.val = ![0, 1, 2, 0] := by funext i; fin_cases i <;> rfl
example : tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyLeft 2)
      (edgeOutput_tupleDegree _ _ (by decide)) = gapTensor ℤ gapOnlyWord 3 :=
  pivotErase_tensor_before ℤ gapOnlyWord 0 2 (by decide) (by decide) (by decide)
example : tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyRight 2)
      (edgeOutput_tupleDegree _ _ (by decide)) = gapTensor ℤ gapOnlyWord 3 :=
  pivotErase_tensor_after ℤ gapOnlyWord 4 2 (by decide) (by decide) (by decide)
-- この空の元切断区間の例の具体的な二係数。一般公式による同じ相殺は下で検証。
example : deletionCoefficient gapOnlyWord.val 0 * edgeSign (erase gapOnlyWord.val 0) 2 = -1 ∧
    deletionCoefficient gapOnlyWord.val 4 * edgeSign (erase gapOnlyWord.val 4) 2 = 1 := by decide

-- 01202 の二削除の相殺を一般の係数・実際のテンソル公式で検証する。
example : (deletionCoefficient gapOnlyWord.val 0 * edgeSign (erase gapOnlyWord.val 0) 2) •
      tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyLeft 2)
        (edgeOutput_tupleDegree _ _ (by decide)) +
    (deletionCoefficient gapOnlyWord.val 4 * edgeSign (erase gapOnlyWord.val 4) 2) •
      tensorVectorOfDegree ℤ 3 2 (edgeOutput gapOnlyRight 2)
        (edgeOutput_tupleDegree _ _ (by decide)) = 0 :=
  pivotDeletion_weighted_pair ℤ gapOnlyWord 0 4 2 2 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
-- 色を置換した20121では区切り色の逆転数が奇数なので、両係数の符号が反転する。
private def gapOddWord : BasisWord 3 2 := ⟨![2, 0, 1, 2, 1], by decide⟩
example : (-1 : ℤ) ^ (Finset.univ.filter (Caesura gapOddWord.val)).card *
    (-1 : ℤ) ^ positionInversionCount gapOddWord.val
      (Finset.univ.filter (Caesura gapOddWord.val)) = -1 := by decide
example : deletionCoefficient gapOddWord.val 0 * edgeSign (erase gapOddWord.val 0) 2 = 1 := by
  have h := pivotDeletion_coefficient_before gapOddWord.val 0 2
    (by decide) (by decide) (by decide)
  have hc : (-1 : ℤ) ^ (Finset.univ.filter (Caesura gapOddWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount gapOddWord.val
        (Finset.univ.filter (Caesura gapOddWord.val)) = -1 := by decide
  simpa only [hc, neg_neg] using h
example : deletionCoefficient gapOddWord.val 4 * edgeSign (erase gapOddWord.val 4) 2 = -1 := by
  have h := pivotDeletion_coefficient_after gapOddWord.val 4 2
    (by decide) (by decide) (by decide)
  have hc : (-1 : ℤ) ^ (Finset.univ.filter (Caesura gapOddWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount gapOddWord.val
        (Finset.univ.filter (Caesura gapOddWord.val)) = -1 := by decide
  simpa only [hc] using h

-- 01202 の全左右削除添字は、それぞれ一つの隙間隣接退化切断へ対応する。
example : Fintype.card (PivotResidualCut.Before gapOnlyWord.val) = 1 := by
  rw [Fintype.card_congr (PivotResidualCut.beforeEquiv (u := gapOnlyWord.val))]
  decide
example : Fintype.card (PivotResidualCut.After gapOnlyWord.val) = 1 := by
  rw [Fintype.card_congr (PivotResidualCut.afterEquiv (u := gapOnlyWord.val))]
  decide
-- 二つの既知項だけでなく、実際の全切断点障害削除和も零になる。
example : ∑ c, pivotResidualValue ℤ gapOnlyWord c = 0 := by
  rw [pivotResidualValue_sum_eq_boundary]
  apply Finset.sum_eq_zero
  intro p _
  have hn : ¬ EdgeNondegenerate gapOnlyWord.val p := by fin_cases p <;> decide
  simp only [pivotBoundaryValue, dite_eq_right hn]
-- 非零元切断が二つある01203でも、全削除和は同じ実際の両端隙間差へ一致する。
example : ∑ c, pivotResidualValue ℤ pivotIntervalWord c =
    -(gapTensor ℤ pivotIntervalWord 1 - gapTensor ℤ pivotIntervalWord 3) := by
  rw [pivotResidualValue_sum_eq_boundary]
  have h := pivotBoundaryValue_sum_of_endpoints ℤ pivotIntervalWord 1 2
    (by decide) (by decide) (by decide)
  have hs : (-1 : ℤ) ^ (Finset.univ.filter (Caesura pivotIntervalWord.val)).card *
      (-1 : ℤ) ^ positionInversionCount pivotIntervalWord.val
        (Finset.univ.filter (Caesura pivotIntervalWord.val)) = -1 := by decide
  simpa only [hs, neg_one_zsmul] using! h

-- 01202 では非切断点・切断点障害を全て含む正規化全削除和が相殺する。
example : ∑ c, normalizedDeletedValue ℤ gapOnlyWord c = 0 :=
  normalizedDeletedValue_sum_eq_zero_of_no_cut ℤ gapOnlyWord (by decide)
-- 三出現の01020でも正規化全削除和が零となる。
example : ∑ c, normalizedDeletedValue ℤ residualWord c = 0 :=
  normalizedDeletedValue_sum_eq_zero_of_no_cut ℤ residualWord (by decide)
-- 元切断が非零の010では、実際の全削除和は元切断非零部分と切断点境界部分へ分かれる。
example : ∑ c, normalizedDeletedValue ℤ compositionInner c =
    (∑ c : NormalizedDeletedCut.Regular compositionInner.val,
      normalizedDeletedValue ℤ compositionInner c.val) +
        ∑ p, pivotBoundaryValue ℤ compositionInner p :=
  normalizedDeletedValue_sum_reduce ℤ compositionInner

-- 非全射な00と、全射だが退化する001は、生成元上の実際の辺成分でも零。
example : edgeComponent ℤ 2 0 (generator ℤ (n := 2) (d := 0) (![0, 0] : Fin 2 → Fin 2)) = 0 := by
  have hn : ¬ Function.Surjective (![0, 0] : Fin 2 → Fin 2) := by decide
  simpa only [dite_eq_right hn] using!
    edgeComponent_generator ℤ (n := 2) (d := 0) (![0, 0] : Fin 2 → Fin 2)
example : edgeComponent ℤ 2 1 (generator ℤ (n := 2) (d := 1) (![0, 0, 1] : Fin 3 → Fin 2)) = 0 := by
  rw [edgeComponent_generator, dite_eq_left (by decide)]
  apply Finset.sum_eq_zero
  intro p _
  have hn : ∀ q : Fin 3, ¬ EdgeNondegenerate (![0, 0, 1] : Fin 3 → Fin 2) q := by decide
  exact False.elim (hn p.val p.property)
-- 正規化和だけでなく、01202と01020の実際の削除微分の辺成分も全体として零。
example : edgeComponent ℤ 3 1 (differentialOnWord ℤ gapOnlyWord) = 0 :=
  edgeComponent_differentialOnWord_eq_zero_of_no_cut ℤ gapOnlyWord (by decide)
example : edgeComponent ℤ 3 1 (differentialOnWord ℤ residualWord) = 0 :=
  edgeComponent_differentialOnWord_eq_zero_of_no_cut ℤ residualWord (by decide)
-- 010の非零元切断部分も、同じ実際の微分成分から直接取り出せる。
example : edgeComponent ℤ 2 0 (differentialOnWord ℤ compositionInner) =
    (∑ c : NormalizedDeletedCut.Regular compositionInner.val,
      normalizedDeletedValue ℤ compositionInner c.val) +
        ∑ p, pivotBoundaryValue ℤ compositionInner p :=
  edgeComponent_differentialOnWord_reduce ℤ compositionInner

-- 010の反復色位置対は一つで、左右二削除が元切断非零部分の全添字となる。
example : Fintype.card (NormalizedDeletedCut.Regular compositionInner.val) = 2 := by
  have hc : Fintype.card (RepeatCutPair compositionInner.val) = 1 := by
    rw [Fintype.card_congr (repeatPairFiberEquiv (u := compositionInner.val))]
    decide
  rw [← Fintype.card_congr (regularCutEquiv compositionInner), Fintype.card_prod, hc]
  decide
-- 010と、交換符号が非自明な20120の実際の辺成分が削除微分と可換する。
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 2).d (-2) (-1)
    (edgeComponentOnWord ℤ compositionInner) =
      edgeComponent ℤ 2 0 (differentialOnWord ℤ compositionInner) := by
  simpa only using! edgeComponentOnWord_d_positive ℤ compositionInner
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d (-3) (-2)
    (edgeComponentOnWord ℤ cutSignWord) =
      edgeComponent ℤ 3 1 (differentialOnWord ℤ cutSignWord) := by
  simpa only using! edgeComponentOnWord_d_positive ℤ cutSignWord
-- 次数零の置換語とarity零の空語も、入力辺の二頂点差へ一致する。
private def zeroPermutationWord : BasisWord 3 0 := ⟨![2, 0, 1], by decide⟩
private def zeroEmptyWord : BasisWord 0 0 := ⟨Fin.elim0, by decide⟩
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d (-1) 0
    (edgeComponentOnWord ℤ zeroPermutationWord) =
      vertexComponentOnWord ℤ zeroPermutationWord 1 -
        vertexComponentOnWord ℤ zeroPermutationWord 0 :=
  edgeComponentOnWord_d_zero ℤ zeroPermutationWord
example : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 0).d (-1) 0
    (edgeComponentOnWord ℤ zeroEmptyWord) =
      vertexComponentOnWord ℤ zeroEmptyWord 1 - vertexComponentOnWord ℤ zeroEmptyWord 0 :=
  edgeComponentOnWord_d_zero ℤ zeroEmptyWord

-- 0102の二削除係数の総和は零。全ての頂点へ送った実際の微分も零。
example : ∑ i : Fin 4, deletionCoefficient compositionOuter.val i = 0 := by decide
example (b : Fin 2) : vertexComponent ℤ 2 0 b (differentialOnWord ℤ compositionInner) = 0 :=
  vertexComponent_differentialOnWord ℤ compositionInner b
example (b : Fin 2) : vertexComponent ℤ 3 0 b (differentialOnWord ℤ compositionOuter) = 0 :=
  vertexComponent_differentialOnWord ℤ compositionOuter b
-- 零次数の置換語・空語の実際の頂点出力は閉じている。
example (b : Fin 2) : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d 0 1
    (vertexComponentOnWord ℤ zeroPermutationWord b) = 0 := by
  simpa only using! vertexComponentOnWord_d_eq_zero ℤ zeroPermutationWord b
example (b : Fin 2) : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 0).d 0 1
    (vertexComponentOnWord ℤ zeroEmptyWord b) = 0 := by
  simpa only using! vertexComponentOnWord_d_eq_zero ℤ zeroEmptyWord b
-- 高い次数でも、実際の頂点微分の両辺は一致する。
example (b : Fin 2) : (SerrePositivity.TensorPowers.power (IntervalCuts.interval ℤ) 3).d (-2) (-1)
    (vertexComponentOnWord ℤ cutSignWord b) =
      vertexComponent ℤ 3 1 b (differentialOnWord ℤ cutSignWord) := by
  simpa only using! vertexComponentOnWord_d_positive ℤ cutSignWord b

-- 任意の二頂点値・一辺値を実際の正規化区間へ延長して評価できる。
example (a b : ℤ) : vertexChainLift ℤ (ModuleCat.of ℤ ℤ)
    (fun i => if i = 0 then a else b) (vertexChain ℤ 0) = a := by
  simpa using! vertexChainLift_vertex ℤ (ModuleCat.of ℤ ℤ)
    (fun i => if i = 0 then a else b) 0
example (a b : ℤ) : vertexChainLift ℤ (ModuleCat.of ℤ ℤ)
    (fun i => if i = 0 then a else b) (vertexChain ℤ 1) = b := by
  simpa using! vertexChainLift_vertex ℤ (ModuleCat.of ℤ ℤ)
    (fun i => if i = 0 then a else b) 1
example (e : ℤ) : edgeChainLift ℤ (ModuleCat.of ℤ ℤ) e (edgeChain ℤ) = e := by
  simpa only using! edgeChainLift_edge ℤ (ModuleCat.of ℤ ℤ) e
-- 実際の整数区間を入力にした双線形成分が、既存の切断値を返す。
example (b : Fin 2) : vertexInputBilinear ℤ 2 1
    (basis ℤ 2 1 (ULift.up compositionInner))
    ((intervalXIso ℤ 0).inv (vertexChain ℤ b)) = 0 := by
  rw [vertexInputBilinear_vertex, vertexComponent_basis]
  exact vertexComponentOnWord_eq_zero_of_positive ℤ compositionInner (by decide) b
example : edgeInputBilinear ℤ 2 1 (basis ℤ 2 1 (ULift.up compositionInner))
    ((intervalXIso ℤ 1).inv (edgeChain ℤ)) = edgeComponentOnWord ℤ compositionInner := by
  rw [edgeInputBilinear_edge, edgeComponent_basis]

-- 整数複体射を実際の区間辺で評価すると、010 の有限切断値を返す。
example : (cochainAction ℤ 2).f (-2)
    (HomologicalComplex.ιTensorObj (Surjection.complex ℤ 2) (interval ℤ)
      (-1) (-1) (-2) (by omega)
      ((Surjection.complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner)) ⊗ₜ[ℤ]
        (intervalXIso ℤ 1).inv (edgeChain ℤ))) =
      edgeComponentOnWord ℤ compositionInner := by
  simpa only [edgeInputBilinear_edge, ModuleCat.hom_inv_apply, edgeComponent_basis] using!
    cochainAction_neg_edge ℤ 2 1
      ((Surjection.complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner)))
      ((intervalXIso ℤ 1).inv (edgeChain ℤ))
-- 同じ正次数語の頂点入力の値は、複体射への組み立て後も零。
example (b : Fin 2) (x : (Surjection.complex ℤ 2).X (-1)) :
    (cochainAction ℤ 2).f (-1)
      (HomologicalComplex.ιTensorObj (Surjection.complex ℤ 2) (interval ℤ)
        (-1) 0 (-1) (by omega) (x ⊗ₜ[ℤ] (intervalXIso ℤ 0).inv (vertexChain ℤ b))) = 0 := by
  simpa only [vertexInputBilinear_eq_zero_of_positive ℤ 2 1 (by decide),
    LinearMap.zero_apply] using!
      cochainAction_neg_vertex ℤ 2 1 x ((intervalXIso ℤ 0).inv (vertexChain ℤ b))
-- 零・−1 以外の区間次数を実際の元について除去できる。
example (y : (interval ℤ).X (-2)) : y = 0 :=
  interval_eq_zero_of_other ℤ (-2) (by decide) (by decide) y
example (y : (interval ℤ).X 1) : y = 0 :=
  interval_eq_zero_of_other ℤ 1 (by decide) (by decide) y

-- 一文字単位の作用は全整数複体の射として単位子と一致する。
example : (complexUnit ℤ ▷ interval ℤ) ≫ cochainAction ℤ 1 ≫
    (SerrePositivity.TensorPowers.oneIso (interval ℤ)).hom = (λ_ (interval ℤ)).hom :=
  cochainAction_unit ℤ
-- 010 の辺の切断は色を交換すると 101 になり、出力の二辺は交換される。
example : Word.rename (Equiv.swap (0 : Fin 2) 1) compositionInner =
    (⟨![1, 0, 1], by decide⟩ : BasisWord 2 1) := by decide
example : edgeSign compositionInner.val 1 = 1 := by decide
example : edgeSign (Word.rename (Equiv.swap (0 : Fin 2) 1) compositionInner).val 1 = -1 := by
  decide
example : edgeOutput (Word.rename (Equiv.swap (0 : Fin 2) 1) compositionInner) 1 =
    edgeOutput compositionInner 1 ∘ (Equiv.swap (0 : Fin 2) 1).symm :=
  edgeOutput_rename _ _ _
example : EdgeNondegenerate (Word.rename (Equiv.swap (0 : Fin 2) 1) compositionInner).val 1 :=
  (edgeNondegenerate_rename_iff _ _ _).mpr (by decide)

-- 実際の非有界複体射として χ の対称列の置換と区間余演算が可換する。
example : ((SerrePositivity.EInfinity.Surjection.sequence ℤ).map
      (SerrePositivity.FiniteBijection.permutation 2 (Equiv.swap (0 : Fin 2) 1)) ▷ interval ℤ) ≫
      cochainAction ℤ 2 =
    cochainAction ℤ 2 ≫ (SerrePositivity.TensorPowers.permutationAction (interval ℤ) 2
      (Equiv.swap (0 : Fin 2) 1)).asIso.hom :=
  cochainAction_equivariance ℤ 2 _
-- 010 の二活動色の中央切断は、隣接色交換で符号を反転する。
example : edgeSign
      (SerrePositivity.Coxeter.adjacentTransposition (0 : Fin 1) ∘ compositionInner.val) 1 =
    edgeSign compositionInner.val 1 * (-1 : ℤ) ^
      (simplexDegree (edgeOutput compositionInner 1 0) *
        simplexDegree (edgeOutput compositionInner 1 1)) :=
  edgeSign_adjacent 0 compositionInner 1 (by decide)
-- 活動色が一つだけなら隣接交換の逆転対の対称差は空となる。
example : (colorCrossPairs (fun i : Fin 1 => (i.castSucc : Fin 2)) Finset.univ 0 1).card = 0 := by
  decide

-- 非零の010切断では指定色0は二出現、切断点色1は一出現。
example : occurrenceCount compositionInner.val (compositionInner.val 1) = 1 :=
  occurrenceCount_pivot_eq_one compositionInner 1 (by decide)
example : edgeOutput compositionInner 1 0 = edge ↔
    (0 : Fin 2) = compositionInner.val 1 ∨ occurrenceCount compositionInner.val 0 = 2 :=
  edgeOutput_eq_edge_iff_pivot_or_two compositionInner 1 (by decide) 0
-- 長さ3の二部分割は三つの共有位置と同値で、中央では部分長2・2。
example : Fintype.card (OverlapPartition 2 3) = 3 := by
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (OverlapPartition.twoEquiv (by decide : 0 < 3))
example : (OverlapPartition.two (1 : Fin 3)).val 0 = 2 := by decide
example : (OverlapPartition.two (1 : Fin 3)).val 1 = 2 := by decide
-- 内側の辺切断は一つ。nullaryは辺入力で消え、頂点入力の二つの項だけが残る。
example : Fintype.card (NestedEdgeCut (m := 1) compositionInner compositionInner 0) = 1 := by
  decide
example : Fintype.card (NestedEdgeCut (m := 1) compositionInner zeroEmptyWord 0) = 0 := by
  decide
example : Fintype.card (NestedEdgeCut (m := 2) zeroPermutationWord zeroEmptyWord 0) = 2 := by
  decide
-- 010の二つの0へ内側010を中央で分けて代入すると01210。元の中央は位置2へ移る。
example : (compositeOuterPosition compositionInner compositionInner 0
    (OverlapPartition.two (1 : Fin 3)) 1 (by decide)).val = 2 := by decide
example : (compositeBasisWord compositionInner compositionInner 0
      (OverlapPartition.two (1 : Fin 3)) (by decide)).val
    (compositeOuterPosition compositionInner compositionInner 0
      (OverlapPartition.two (1 : Fin 3)) 1 (by decide)) = 2 := by decide

-- 010の切断点色1へ内側010の中央切断を挿入する一出現の二段切断。
private def nestedPivotExample : NestedEdgeCut (m := 1) compositionInner compositionInner 1 :=
  NestedEdgeCut.ofEdge 1 (by decide) (by decide) 1 (by decide)
example : nestedPivotExample.partition.val ⟨0, by decide⟩ = 3 := by decide
example : nestedPivotExample.compositePosition.val = 2 := by decide
-- 構成した有限位置は、実際の合成基底語01210の非零切断となる。
example : EdgeNondegenerate
    (compositeBasisWord compositionInner compositionInner 1 nestedPivotExample.partition
      (by decide)).val nestedPivotExample.compositePosition :=
  NestedEdgeCut.compositePosition_pivot_nondegenerate nestedPivotExample (by decide) 1 rfl rfl
example : (compositeBasisWord compositionInner compositionInner 1 nestedPivotExample.partition
      (by decide)).val nestedPivotExample.compositePosition = 2 := by
  simpa only using! NestedEdgeCut.compositePosition_pivot_value nestedPivotExample
    (by decide) 1 rfl rfl
-- 左右での重複消滅は、同じ合成切断の非退化性と一致する。
example : EdgeNondegenerate compositionInner.val 1 ↔
    ((List.ofFn compositionInner.val).take 2).Nodup ∧
      ((List.ofFn compositionInner.val).drop 1).Nodup :=
  edgeNondegenerate_iff_list_nodup compositionInner.val 1

-- 二出現色0へ内側010の中央切断を代入しても非零合成切断となる。
private def nestedRepeatedExample : NestedEdgeCut (m := 1) compositionInner compositionInner 0 :=
  NestedEdgeCut.ofEdge 1 (by decide) (by decide) 1 (by decide)
example : EdgeNondegenerate
    (compositeBasisWord compositionInner compositionInner 0 nestedRepeatedExample.partition
      (by decide)).val nestedRepeatedExample.compositePosition :=
  NestedEdgeCut.compositePosition_nondegenerate nestedRepeatedExample (by decide)
example : nestedRepeatedExample.compositePosition.val = 2 := by decide
-- 頂点出力への零語次数の挿入も同じ写像で非零切断へ送る。
private def nestedVertexExample : NestedEdgeCut (m := 2) zeroPermutationWord
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 :=
  NestedEdgeCut.ofVertex 0 (by decide) (by decide) rfl
example : nestedVertexExample.compositePosition.val = 0 := by decide
example : EdgeNondegenerate
    (compositeBasisWord zeroPermutationWord (permutationWord (1 : Equiv.Perm (Fin 2))) 0
      nestedVertexExample.partition (by decide)).val nestedVertexExample.compositePosition :=
  NestedEdgeCut.compositePosition_nondegenerate nestedVertexExample (by decide)
-- 対応は型全体で単射。両側の有限個数も二出現例では1、零語次数例では4。
example : Function.Injective (NestedEdgeCut.toCompositeCut (u := compositionInner)
    (v := compositionInner) (k := 0) (by decide)) :=
  NestedEdgeCut.toCompositeCut_injective (by decide)
example : Fintype.card (CompositeEdgeCut (m := 1) compositionInner compositionInner 0
    (by decide)) = 1 := by decide
example : Fintype.card (NestedEdgeCut (m := 2) zeroPermutationWord
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0) = 4 := by decide
example : Fintype.card (CompositeEdgeCut (m := 2) zeroPermutationWord
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 (by decide)) = 4 := by decide

-- 残り色の count は零 arity・部分語不足でも保存される。
example : (substitute (m := 1) (n := 0) 0 [1, 0, 1, 0] []).count
    (BarrattEccles.remainingPosition 1 0 0 ⟨1, by decide⟩) = 2 := by
  simpa only using! remaining_count_substitute (n := 0) 0 ⟨1, by decide⟩ [1, 0, 1, 0] []
-- 外側010の色1は、色0への二部分割代入後も一出現。
example : occurrenceCount
    (compositeBasisWord compositionInner compositionInner 0 nestedRepeatedExample.partition
      (by decide)).val (BarrattEccles.remainingPosition 1 2 0 ⟨1, by decide⟩) = 1 := by
  simpa only using! composite_remaining_occurrenceCount compositionInner compositionInner 0
    nestedRepeatedExample.partition (by decide) ⟨1, by decide⟩
-- 一出現挿入の内側切断は、元の二つの非零切断と同値。
example : EdgeNondegenerate
    (compositeBasisWord compositionInner compositionInner 1 nestedPivotExample.partition
      (by decide)).val
      (compositeInnerPosition compositionInner compositionInner 1 nestedPivotExample.partition
        (by decide) 1 rfl 1) ↔
    EdgeNondegenerate compositionInner.val 1 ∧ EdgeNondegenerate compositionInner.val 1 :=
  composite_single_slot_cut_nondegenerate_iff compositionInner compositionInner 1
    nestedPivotExample.partition (by decide) 1 rfl 1 (by decide)
-- 非切断点色への一出現挿入からも外側の非零性を戻せる。
example : EdgeNondegenerate zeroPermutationWord.val 0 :=
  outer_cut_nondegenerate_of_single_slot zeroPermutationWord
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 nestedVertexExample.partition (by decide)
    0 (by decide) (by decide) (by decide)

-- 二部分割の共有端点は合成語01210の位置1と3にあり、非零切断2を跨ぐ。
example : (compositeSegmentLast compositionInner compositionInner 0
    nestedRepeatedExample.partition (by decide) ⟨0, by decide⟩).val = 1 := by decide
example : (compositeSegmentFirst compositionInner compositionInner 0
    nestedRepeatedExample.partition (by decide) ⟨1, by decide⟩).val = 3 := by decide
example : compositeSegmentLast compositionInner compositionInner 0
      nestedRepeatedExample.partition (by decide) ⟨0, by decide⟩ <
      nestedRepeatedExample.compositePosition ∧
    nestedRepeatedExample.compositePosition < compositeSegmentFirst compositionInner
      compositionInner 0 nestedRepeatedExample.partition (by decide) ⟨1, by decide⟩ :=
  compositeSegment_boundary_straddles compositionInner compositionInner 0
    nestedRepeatedExample.partition (by decide) _
    (NestedEdgeCut.compositePosition_nondegenerate nestedRepeatedExample (by decide))
    ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
-- 挿入ラベル切断点は、実際の有限対応の像に戻る。
example : ∃ a : NestedEdgeCut (m := 1) compositionInner compositionInner 1,
    a.toCompositeCut (by decide) = nestedPivotExample.toCompositeCut (by decide) :=
  exists_preimage_of_inserted_pivot compositionInner compositionInner 1 (by decide)
    (nestedPivotExample.toCompositeCut (by decide)) 1 (by decide)

-- 全射性は切断点の色を指定せずに型全体で成立する。
example : Function.Surjective (NestedEdgeCut.toCompositeCut (u := compositionInner)
    (v := compositionInner) (k := 0) (by decide)) :=
  NestedEdgeCut.toCompositeCut_surjective (by decide)
-- 有限同値の順方向は以前構成した実際の切断位置への写像そのもの。
example : NestedEdgeCut.compositeCutEquiv (by decide) nestedRepeatedExample =
    nestedRepeatedExample.toCompositeCut (by decide) := rfl
example : (NestedEdgeCut.compositeCutEquiv (by decide)).symm
    (nestedVertexExample.toCompositeCut (by decide)) = nestedVertexExample :=
  (NestedEdgeCut.compositeCutEquiv (by decide)).symm_apply_apply nestedVertexExample
-- 元の二部分割の共有位置は内側010の非零切断となる。
example : EdgeNondegenerate compositionInner.val
    (OverlapPartition.twoCut (by decide)
      (cast (congrArg (fun t => OverlapPartition t 3) (by decide :
        occurrenceCount compositionInner.val (0 : Fin 2) = 2)) nestedRepeatedExample.partition)) :=
  inner_two_cut_nondegenerate_of_composite compositionInner compositionInner 0
    nestedRepeatedExample.partition (by decide) (by decide) _
    (NestedEdgeCut.compositePosition_nondegenerate nestedRepeatedExample (by decide))

-- 実際の整数係数の合成辺成分も同じ二段切断で添字変更できる。
example : edgeComponent ℤ 3 2 (compositionOnWords ℤ compositionInner compositionInner 0) =
    ∑ a : NestedEdgeCut (m := 1) compositionInner compositionInner 0,
      compositionEdgeCutTerm ℤ compositionInner compositionInner 0 a.partition
        (by decide) a.compositePosition :=
  edgeComponent_composition_nested_cut_sum ℤ compositionInner compositionInner 0 (by decide)

-- 一出現の切断点色・二出現の非切断点色の両分岐で全出力は三本の辺。
example : List.ofFn nestedPivotExample.outputFamily = [edge, edge, edge] := by decide
example : List.ofFn nestedRepeatedExample.outputFamily = [edge, edge, edge] := by decide
-- 頂点入力の右側・左側の双方を確認する。
example : List.ofFn nestedVertexExample.outputFamily = [vertex 1, vertex 1, vertex 1, edge] :=
  by decide
private def nestedVertexLeftExample : NestedEdgeCut (m := 2) zeroPermutationWord
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 :=
  NestedEdgeCut.ofVertex 2 (by decide) (by decide) rfl
example : List.ofFn nestedVertexLeftExample.outputFamily = [vertex 0, vertex 0, edge, vertex 0] :=
  by decide
-- 合成語での全色の出力と、二段作用の指定した全出力族の一致。
example : edgeOutput
    (compositeBasisWord compositionInner compositionInner 0 nestedRepeatedExample.partition
      (by decide)) nestedRepeatedExample.compositePosition = nestedRepeatedExample.outputFamily :=
  NestedEdgeCut.compositePosition_outputFamily nestedRepeatedExample (by decide)
example : tupleDegree 3 nestedPivotExample.outputFamily = 3 :=
  NestedEdgeCut.outputFamily_tupleDegree nestedPivotExample (by decide)
-- 元の合成符号を保った実際の面テンソル和としても同じ出力族へ移る。
example : edgeComponent ℤ 3 2 (compositionOnWords ℤ compositionInner compositionInner 0) =
    ∑ a : NestedEdgeCut (m := 1) compositionInner compositionInner 0,
      (compositionSign compositionInner compositionInner 0 a.partition *
        edgeSign (compositeBasisWord compositionInner compositionInner 0 a.partition
          (by decide)).val a.compositePosition) •
        tensorVectorOfDegree ℤ 3 3 a.outputFamily (a.outputFamily_tupleDegree (by decide)) :=
  edgeComponent_composition_nested_output_sum ℤ compositionInner compositionInner 0 (by decide)

-- 非零切断の前半だけが内側次数を全て持ち、後半の行次数は零。
example : segmentDegree compositionInner.val (OverlapPartition.two (1 : Fin 3)) 0 = 1 :=
  segmentDegree_two_zero compositionInner 1 (by decide)
example : segmentDegree compositionInner.val (OverlapPartition.two (1 : Fin 3)) 1 = 0 :=
  segmentDegree_two_one compositionInner 1 (by decide)
example : caesuraRank compositionInner.val 1 = 1 :=
  caesuraRank_pivot_eq_degree compositionInner 1 (by decide)
-- 同じ内外語でも切断点色への代入は正、二出現色への代入は負となる。
example : compositionSign compositionInner compositionInner 1 nestedPivotExample.partition = 1 :=
  NestedEdgeCut.compositionSign_pivot nestedPivotExample rfl
example : compositionSign compositionInner compositionInner 0 nestedRepeatedExample.partition =
    (-1 : ℤ) := by
  simpa only using! NestedEdgeCut.compositionSign_nonpivot nestedRepeatedExample 1 rfl (by decide)
example : compositionSign zeroPermutationWord (permutationWord (1 : Equiv.Perm (Fin 2))) 0
    nestedVertexExample.partition = 1 :=
  NestedEdgeCut.compositionSign_vertex nestedVertexExample rfl

-- 実際の面テンソルの連結は、空の前方列と二つの辺を含む。
example : (SerrePositivity.TensorPowers.appendIso (interval ℤ) 0 1).hom.f (-1)
    (HomologicalComplex.ιTensorObj (SerrePositivity.TensorPowers.power (interval ℤ) 0)
      (SerrePositivity.TensorPowers.power (interval ℤ) 1) 0 (-1) (-1) rfl
      (tensorVector ℤ 0 Fin.elim0 ⊗ₜ[ℤ] tensorVector ℤ 1 (fun _ => edge))) =
    tensorVectorAt ℤ 1 (Fin.append Fin.elim0 (fun _ : Fin 1 => edge)) (-1) (by decide) :=
  appendIso_tensorVector ℤ 0 1 Fin.elim0 (fun _ => edge) (-1) (by decide)
example : (SerrePositivity.TensorPowers.appendIso (interval ℤ) 1 1).hom.f (-2)
    (HomologicalComplex.ιTensorObj (SerrePositivity.TensorPowers.power (interval ℤ) 1)
      (SerrePositivity.TensorPowers.power (interval ℤ) 1) (-1) (-1) (-2) rfl
      (tensorVector ℤ 1 (fun _ => edge) ⊗ₜ[ℤ] tensorVector ℤ 1 (fun _ => edge))) =
    tensorVectorAt ℤ 2 (Fin.append (fun _ : Fin 1 => edge) (fun _ : Fin 1 => edge))
      (-2) (by decide) :=
  appendIso_tensorVector ℤ 1 1 (fun _ => edge) (fun _ => edge) (-2) (by decide)

-- 係数と前方の次数がともに−1なら、実際のブロック余代入には負符号が付く。
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
example (K C : Complex ℤ) (θ : C ⊗ K ⟶ power K 2) (a : C.X (-1))
    (x : (power K 1).X (-1)) (y : K.X (-1)) (w : (power K 0).X 0) :
    (coInsertionBlocks K C 1 2 0 θ).f (-3)
      (ιTensorObj C (power K 1 ⊗ (K ⊗ power K 0)) (-1) (-2) (-3) rfl
        (a ⊗ₜ[ℤ] ιTensorObj (power K 1) (K ⊗ power K 0) (-1) (-1) (-2) rfl
          (x ⊗ₜ[ℤ] ιTensorObj K (power K 0) (-1) 0 (-1) rfl (y ⊗ₜ[ℤ] w)))) =
      -(appendIso K 1 2).hom.f (-3)
        (ιTensorObj (power K 1) (power K 2) (-1) (-2) (-3) rfl
          (x ⊗ₜ[ℤ] (appendIso K 2 0).hom.f (-2)
            (ιTensorObj (power K 2) (power K 0) (-2) 0 (-2) rfl
              (θ.f (-2) (ιTensorObj C K (-1) (-1) (-2) rfl (a ⊗ₜ[ℤ] y)) ⊗ₜ[ℤ] w)))) := by
  simpa only [show (-1 : ℤ) * (-1) = 1 by decide, Int.negOnePow_one,
    Units.smul_def, Units.coe_neg_one, neg_one_zsmul] using!
    coInsertionBlocks_apply K C 1 2 0 θ (-1) (-1) (-1) 0 (-3) rfl a x y w

-- 元の族の指定因子の前後と、正・零 arity の置換を同じ順序で扱う。
private def outerFaceFixture : Fin 3 → Simplex := ![edge, edge, vertex 1]
private def innerFaceFixture : Fin 2 → Simplex := fun _ => edge
example : List.ofFn (prefixFamily outerFaceFixture 1) = [edge] := by decide
example : List.ofFn (suffixFamily outerFaceFixture 1) = [vertex 1] := by decide
example : List.ofFn (insertionFamily outerFaceFixture innerFaceFixture 1) =
    [edge, edge, edge, vertex 1] := by decide
example : List.ofFn (insertionFamily outerFaceFixture (n := 0) Fin.elim0 1) =
    [edge, vertex 1] := by decide
example : tupleDegree 1 (prefixFamily outerFaceFixture 1) = prefixDegree 3 outerFaceFixture 1 :=
  tupleDegree_prefixFamily outerFaceFixture 1
-- 二段作用の内側族の次数も、内側語次数と実際の指定入力次数の和。
example : tupleDegree 2 nestedRepeatedExample.innerOutputFamily =
    1 + simplexDegree (edgeOutput compositionInner nestedRepeatedExample.val.1 0) :=
  NestedEdgeCut.innerOutputFamily_tupleDegree nestedRepeatedExample

-- ブロック表示を経ず、元の面テンソルへ実際の余代入を施す場合にも奇数交換は負。
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
example (C : Complex ℤ) (θ : C ⊗ interval ℤ ⟶ power (interval ℤ) 2) (a : C.X (-1)) (r : ℤ)
    (hθ : θ.f (-2) (ιTensorObj C (interval ℤ) (-1) (-1) (-2) rfl
      (a ⊗ₜ[ℤ] faceVector ℤ edge)) = r • tensorVectorAt ℤ 2 innerFaceFixture (-2) (by decide)) :
    (tensorCoInsertionAction (interval ℤ) C 2 2 1 θ).f (-3)
      (ιTensorObj C (power (interval ℤ) 3) (-1) (-2) (-3) rfl
        (a ⊗ₜ[ℤ] tensorVectorAt ℤ 3 outerFaceFixture (-2) (by decide))) =
      -(r • tensorVectorAt ℤ 4 (insertionFamily outerFaceFixture innerFaceFixture 1)
        (-3) (by decide)) := by
  have hs : ((-1 : ℤ) * -(prefixDegree 3 outerFaceFixture 1 : ℤ)).negOnePow =
      (-1 : ℤˣ) := by decide
  simpa only [hs, Units.smul_def, Units.coe_neg_one, neg_one_zsmul] using!
    tensorCoInsertionAction_face_apply ℤ C 2 2 1 θ (-1) (-3) outerFaceFixture
      innerFaceFixture (by decide) a (by decide) r hθ

-- 正次数の頂点入力は空、空語の頂点入力と語010の辺入力は各一項。
example : Fintype.card (FaceCut compositionInner (vertex 0)) = 0 := by decide
example : Fintype.card (FaceCut zeroEmptyWord (vertex 1)) = 1 := by decide
example : Fintype.card (FaceCut zeroEmptyWord edge) = 0 := by decide
example : Fintype.card (FaceCut compositionInner edge) = 1 := by decide
-- 同じ二段切断の内側面出力・符号を、依存対表示で保持する。
example : (NestedEdgeCut.faceCutEquiv compositionInner compositionInner 0
    nestedRepeatedExample).2.coefficient = 1 := by decide
example : List.ofFn (NestedEdgeCut.faceCutEquiv compositionInner compositionInner 0
    nestedRepeatedExample).2.output = [edge, edge] := by decide
example : nestedRepeatedExample.outputFamily = insertionFamily
    (edgeOutput compositionInner nestedRepeatedExample.val.1)
    (NestedEdgeCut.faceCutEquiv compositionInner compositionInner 0
      nestedRepeatedExample).2.output 0 :=
  NestedEdgeCut.outputFamily_eq_faceCut nestedRepeatedExample

-- 同じ内外語でも、指定色0では係数交換が負、切断点色1では前方交換と相殺。
example : nestedRepeatedExample.actionCoefficient = -1 := by decide
example : nestedPivotExample.actionCoefficient = 1 := by decide
example : nestedVertexExample.actionCoefficient = 1 := by decide
example : tupleDegree 3 nestedRepeatedExample.outputFamily = 3 :=
  NestedEdgeCut.outputFamily_tupleDegree_all nestedRepeatedExample

-- 二段作用の実際の全複体射でも、語010の色0への代入は負の三辺テンソル。
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
private lemma iteratedRepeatedEdgeFixture : (iteratedCochainAction ℤ 1 2 0).f (-3)
    (ιTensorObj (complex ℤ 2 ⊗ complex ℤ 2) (interval ℤ) (-2) (-1) (-3) (by decide)
      (ιTensorObj (complex ℤ 2) (complex ℤ 2) (-1) (-1) (-2) (by decide)
        ((complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner)) ⊗ₜ[ℤ]
          (complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner))) ⊗ₜ[ℤ]
        faceVector ℤ edge)) =
    -(tensorVectorAt ℤ 3 nestedRepeatedExample.outputFamily (-3) (by decide)) := by
  have H := iteratedCochainAction_basis_edge_nested_sum ℤ compositionInner compositionInner
    0 (-3) (by decide)
  have hu : ∀ a : NestedEdgeCut (m := 1) compositionInner compositionInner 0,
      a = nestedRepeatedExample := by decide
  rw [Finset.sum_eq_single nestedRepeatedExample (fun a _ ha => False.elim (ha (hu a)))
    (by simp)] at H
  have hc : nestedRepeatedExample.actionCoefficient = -1 := by decide
  simpa only [hc, neg_one_zsmul] using! H

-- 内側の両頂点入力で、外側の逆転による負符号を保つ。外側次数は一。
private def vertexSignOuterRight : BasisWord 3 1 := ⟨![2, 1, 2, 0], by decide⟩
private def vertexSignOuterLeft : BasisWord 3 1 := ⟨![0, 2, 1, 2], by decide⟩
private def vertexSignRightCut : NestedEdgeCut (m := 2) vertexSignOuterRight
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 :=
  NestedEdgeCut.ofVertex 1 (by decide) (by decide) rfl
private def vertexSignLeftCut : NestedEdgeCut (m := 2) vertexSignOuterLeft
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 :=
  NestedEdgeCut.ofVertex 2 (by decide) (by decide) rfl
example : edgeOutput vertexSignOuterRight vertexSignRightCut.val.1 0 = vertex 1 := by decide
example : edgeOutput vertexSignOuterLeft vertexSignLeftCut.val.1 0 = vertex 0 := by decide
example : vertexSignRightCut.actionCoefficient = -1 := by decide
example : vertexSignLeftCut.actionCoefficient = -1 := by decide
example : List.ofFn vertexSignRightCut.outputFamily =
    [vertex 1, vertex 1, edge, edge] := by decide
example : List.ofFn vertexSignLeftCut.outputFamily =
    [vertex 0, vertex 0, edge, edge] := by decide
example : (activePositions vertexSignOuterLeft.val vertexSignLeftCut.val.1).image
    vertexSignLeftCut.remainingPositionMap =
      activePositions (compositeBasisWord vertexSignOuterLeft
        (permutationWord (1 : Equiv.Perm (Fin 2))) 0 vertexSignLeftCut.partition
          (by decide)).val vertexSignLeftCut.compositePosition := by decide
example : compositionSign vertexSignOuterRight (permutationWord (1 : Equiv.Perm (Fin 2)))
    0 vertexSignRightCut.partition * edgeSign (compositeBasisWord vertexSignOuterRight
      (permutationWord (1 : Equiv.Perm (Fin 2))) 0 vertexSignRightCut.partition
        (by decide)).val vertexSignRightCut.compositePosition = vertexSignRightCut.actionCoefficient :=
  NestedEdgeCut.compositionCoefficient_vertex vertexSignRightCut (by decide) rfl
example : compositionEdgeCutTerm ℤ vertexSignOuterLeft
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 vertexSignLeftCut.partition (by decide)
      vertexSignLeftCut.compositePosition =
    vertexSignLeftCut.actionCoefficient • tensorVectorOfDegree ℤ 4 2
      vertexSignLeftCut.outputFamily vertexSignLeftCut.outputFamily_tupleDegree_all :=
  NestedEdgeCut.compositionEdgeCutTerm_vertex ℤ vertexSignLeftCut (by decide) rfl

-- 切断点色への挿入で交差逆転が三つある次数二の内側語と、負の内側切断符号。
private def pivotCrossOuter : BasisWord 2 1 := ⟨![1, 0, 1], by decide⟩
private def pivotCrossInner : BasisWord 3 2 := ⟨![0, 1, 2, 0, 1], by decide⟩
private def pivotCrossCut : NestedEdgeCut (m := 1) pivotCrossOuter pivotCrossInner 0 :=
  NestedEdgeCut.ofEdge 1 (by decide) (by decide) 2 (by decide)
private def pivotNegativeInnerCut : NestedEdgeCut (m := 1) compositionInner pivotCrossOuter 1 :=
  NestedEdgeCut.ofEdge 1 (by decide) (by decide) 1 (by decide)
example : pivotCrossCut.actionCoefficient = -1 := by decide
example : positionInversionCount (compositeBasisWord pivotCrossOuter pivotCrossInner 0
    pivotCrossCut.partition (by decide)).val
      (activePositions (compositeBasisWord pivotCrossOuter pivotCrossInner 0
        pivotCrossCut.partition (by decide)).val pivotCrossCut.compositePosition) = 3 := by decide
example : ((activePositions pivotCrossOuter.val pivotCrossCut.val.1).erase
    pivotCrossCut.val.1).image pivotCrossCut.remainingPositionMap ∪
      (activePositions pivotCrossInner.val 2).image (pivotCrossCut.pivotInnerMap rfl) =
    activePositions (compositeBasisWord pivotCrossOuter pivotCrossInner 0 pivotCrossCut.partition
      (by decide)).val pivotCrossCut.compositePosition := by decide
example : compositionSign pivotCrossOuter pivotCrossInner 0 pivotCrossCut.partition *
    edgeSign (compositeBasisWord pivotCrossOuter pivotCrossInner 0 pivotCrossCut.partition
      (by decide)).val pivotCrossCut.compositePosition = pivotCrossCut.actionCoefficient :=
  NestedEdgeCut.compositionCoefficient_pivot pivotCrossCut (by decide) 2 rfl rfl
example : pivotNegativeInnerCut.actionCoefficient = -1 := by decide
example : edgeSign (compositeBasisWord compositionInner pivotCrossOuter 1
    pivotNegativeInnerCut.partition (by decide)).val pivotNegativeInnerCut.compositePosition = -1 :=
  by decide
example : compositionEdgeCutTerm ℤ compositionInner pivotCrossOuter 1 pivotNegativeInnerCut.partition
    (by decide) pivotNegativeInnerCut.compositePosition =
    pivotNegativeInnerCut.actionCoefficient • tensorVectorOfDegree ℤ 3 3
      pivotNegativeInnerCut.outputFamily pivotNegativeInnerCut.outputFamily_tupleDegree_all :=
  NestedEdgeCut.compositionEdgeCutTerm_pivot ℤ pivotNegativeInnerCut (by decide) 1 rfl rfl

-- 第一指定出現の前後に活動位置があり、内側次数二で合成逆転数が七つになる例。
private def nonpivotCrossOuter : BasisWord 4 2 := ⟨![3, 1, 0, 3, 1, 2], by decide⟩
private def nonpivotCrossCut : NestedEdgeCut (m := 3) nonpivotCrossOuter pivotCrossInner 1 :=
  NestedEdgeCut.ofEdge 2 (by decide) (by decide) 2 (by decide)
example : nonpivotCrossCut.actionCoefficient = -1 := by decide
example : (nonpivotCrossCut.nonpivotInnerMap 2 rfl (by decide) 2).val = 3 := by decide
example : positionInversionCount (compositeBasisWord nonpivotCrossOuter pivotCrossInner 1
    nonpivotCrossCut.partition (by decide)).val
      (activePositions (compositeBasisWord nonpivotCrossOuter pivotCrossInner 1
        nonpivotCrossCut.partition (by decide)).val nonpivotCrossCut.compositePosition) = 7 :=
  by decide
example : List.ofFn nonpivotCrossCut.outputFamily =
    [edge, edge, edge, edge, vertex 1, edge] := by decide
example : compositionSign nonpivotCrossOuter pivotCrossInner 1 nonpivotCrossCut.partition *
    edgeSign (compositeBasisWord nonpivotCrossOuter pivotCrossInner 1 nonpivotCrossCut.partition
      (by decide)).val nonpivotCrossCut.compositePosition = nonpivotCrossCut.actionCoefficient :=
  NestedEdgeCut.compositionCoefficient nonpivotCrossCut (by decide)
example : compositionEdgeCutTerm ℤ nonpivotCrossOuter pivotCrossInner 1 nonpivotCrossCut.partition
    (by decide) nonpivotCrossCut.compositePosition =
    nonpivotCrossCut.actionCoefficient • tensorVectorOfDegree ℤ 6 5 nonpivotCrossCut.outputFamily
      nonpivotCrossCut.outputFamily_tupleDegree_all :=
  NestedEdgeCut.compositionEdgeCutTerm_nonpivot ℤ nonpivotCrossCut (by decide) 2 rfl (by decide)

-- 実際の部分合成射を先に施す左辺も、先に二段作用を施す右辺と同じ負の値。
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
example : ((complexPartialComposition ℤ 1 2 0 ▷ interval ℤ) ≫ cochainAction ℤ 3).f (-3)
    (ιTensorObj (complex ℤ 2 ⊗ complex ℤ 2) (interval ℤ) (-2) (-1) (-3) (by decide)
      (ιTensorObj (complex ℤ 2) (complex ℤ 2) (-1) (-1) (-2) (by decide)
        ((complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner)) ⊗ₜ[ℤ]
          (complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner))) ⊗ₜ[ℤ]
        faceVector ℤ edge)) =
    -(tensorVectorAt ℤ 3 nestedRepeatedExample.outputFamily (-3) (by decide)) := by
  exact (cochainAction_composition_basis_edge_eq_iterated ℤ compositionInner compositionInner 0
    (by decide)).trans iteratedRepeatedEdgeFixture

-- 語基底と元の両頂点で、次数零の実際の合成は同じ一定頂点テンソル。
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
example (b : Fin 2) : ((complexPartialComposition ℤ 2 2 2 ▷ interval ℤ) ≫
    cochainAction ℤ 4).f 0
    (ιTensorObj (complex ℤ 3 ⊗ complex ℤ 2) (interval ℤ) 0 0 0 rfl
      (ιTensorObj (complex ℤ 3) (complex ℤ 2) 0 0 0 rfl
        ((complexXIso ℤ 3 0).inv (basis ℤ 3 0 (ULift.up zeroPermutationWord)) ⊗ₜ[ℤ]
          (complexXIso ℤ 2 0).inv (basis ℤ 2 0
            (ULift.up (permutationWord (Equiv.swap (0 : Fin 2) 1))))) ⊗ₜ[ℤ]
        faceVector ℤ (vertex b))) =
    tensorVectorAt ℤ 4 (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) :=
  (cochainAction_composition_basis_vertex_eq_iterated ℤ zeroPermutationWord
    (permutationWord (Equiv.swap (0 : Fin 2) 1)) 2 (by decide) b).trans
      (iteratedCochainAction_basis_vertex_zero ℤ zeroPermutationWord
        (permutationWord (Equiv.swap (0 : Fin 2) 1)) 2 b)

-- 外側だけ、内側だけが正次数の場合も、両頂点で実際の合成射の値は零。
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
example (b : Fin 2) : ((complexPartialComposition ℤ 1 2 0 ▷ interval ℤ) ≫
    cochainAction ℤ 3).f (-1)
    (ιTensorObj (complex ℤ 2 ⊗ complex ℤ 2) (interval ℤ) (-1) 0 (-1) (by decide)
      (ιTensorObj (complex ℤ 2) (complex ℤ 2) (-1) 0 (-1) (by decide)
        ((complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner)) ⊗ₜ[ℤ]
          (complexXIso ℤ 2 0).inv (basis ℤ 2 0
            (ULift.up (permutationWord (1 : Equiv.Perm (Fin 2)))))) ⊗ₜ[ℤ]
        faceVector ℤ (vertex b))) = 0 :=
  (cochainAction_composition_basis_vertex_eq_iterated ℤ compositionInner
    (permutationWord (1 : Equiv.Perm (Fin 2))) 0 (by decide) b).trans
      (iteratedCochainAction_basis_vertex_outer_positive ℤ compositionInner
        (permutationWord (1 : Equiv.Perm (Fin 2))) 0 b (by decide))
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
example (b : Fin 2) : ((complexPartialComposition ℤ 2 2 1 ▷ interval ℤ) ≫
    cochainAction ℤ 4).f (-1)
    (ιTensorObj (complex ℤ 3 ⊗ complex ℤ 2) (interval ℤ) (-1) 0 (-1) (by decide)
      (ιTensorObj (complex ℤ 3) (complex ℤ 2) 0 (-1) (-1) (by decide)
        ((complexXIso ℤ 3 0).inv (basis ℤ 3 0 (ULift.up zeroPermutationWord)) ⊗ₜ[ℤ]
          (complexXIso ℤ 2 1).inv (basis ℤ 2 1 (ULift.up compositionInner))) ⊗ₜ[ℤ]
        faceVector ℤ (vertex b))) = 0 :=
  (cochainAction_composition_basis_vertex_eq_iterated ℤ zeroPermutationWord compositionInner
    1 (by decide) b).trans
      (iteratedCochainAction_basis_vertex_inner_positive ℤ zeroPermutationWord compositionInner
        1 b (by decide) (-1) (by decide))

-- nullary の内側次数零余代入の右辺は、一定頂点族から指定因子を除く。
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers HomologicalComplex in
example (b : Fin 2) :
    (tensorCoInsertionAction (interval ℤ) (complex ℤ 0) 2 0 1 (cochainAction ℤ 0)).f 0
      (ιTensorObj (complex ℤ 0) (power (interval ℤ) 3) 0 0 0 rfl
        ((complexXIso ℤ 0 0).inv (basis ℤ 0 0 (ULift.up zeroEmptyWord)) ⊗ₜ[ℤ]
          tensorVectorAt ℤ 3 (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl))) =
      tensorVectorAt ℤ 2 (fun _ => vertex b) 0 (by rw [vertex_tupleDegree]; rfl) :=
  tensorCoInsertionAction_basis_vertex_zero_degree ℤ zeroEmptyWord 1 b

-- 基底以外の任意の同次数二元の線形結合でも、実際の全複体射の合成則を使える。
example (z : ℤ) (x y : ((complex ℤ 3 ⊗ complex ℤ 3) ⊗ interval ℤ).X z)
    (a b : ℤ) :
    ((complexPartialComposition ℤ 2 3 1 ▷ interval ℤ) ≫ cochainAction ℤ 5).f z
      (a • x + b • y) =
        a • (iteratedCochainAction ℤ 2 3 1).f z x +
          b • (iteratedCochainAction ℤ 2 3 1).f z y := by
  rw [cochainAction_comp_positive ℤ 2 3 1 (by decide)]
  simp only [map_add, map_zsmul]

-- 内側が空語でも負の切断符号と残り二辺を保持する。
private def nullaryNegativeCut : NestedEdgeCut (m := 2) vertexSignOuterRight zeroEmptyWord 0 :=
  NestedEdgeCut.ofVertex 1 (by decide) (by decide) rfl
private def nullaryNegativePartition :
    OverlapPartition (occurrenceCount vertexSignOuterRight.val 0) 0 :=
  OverlapPartition.single 0
example : nullaryNegativeCut.actionCoefficient = -1 := by decide
example : List.ofFn nullaryNegativeCut.outputFamily = [edge, edge] := by decide
example : List.ofFn (nullaryRawWord vertexSignOuterRight zeroEmptyWord 0
    nullaryNegativePartition) = [1, 0, 1] := by decide

-- 左辺そのものの空語合成も同じ負の二辺テンソルを与える。
example : ((complexPartialComposition ℤ 2 0 0 ▷ interval ℤ) ≫ cochainAction ℤ 2).f (-2)
    (wordPairEdgeInput ℤ vertexSignOuterRight zeroEmptyWord) =
      -(tensorVectorAt ℤ 2 nullaryNegativeCut.outputFamily (-2) (by decide)) := by
  refine (cochainAction_composition_basis_edge ℤ vertexSignOuterRight zeroEmptyWord 0).trans ?_
  rw [edgeComponent_composition_nullary_action_sum ℤ vertexSignOuterRight zeroEmptyWord 0
    nullaryNegativePartition]
  have hu : ∀ a : NestedEdgeCut (m := 2) vertexSignOuterRight zeroEmptyWord 0,
      a = nullaryNegativeCut := by decide
  rw [Finset.sum_eq_single nullaryNegativeCut (fun a _ ha => False.elim (ha (hu a))) (by simp)]
  have hc : nullaryNegativeCut.actionCoefficient = -1 := by decide
  simp only [hc, neg_one_zsmul]
  rfl

-- 唯一出現を削除して隣接退化する語は、正規化前の切断型も空。
private def nullaryDegeneratePartition :
    OverlapPartition (occurrenceCount compositionInner.val 1) 0 := OverlapPartition.single 0
example : List.ofFn (nullaryRawWord compositionInner zeroEmptyWord 1
    nullaryDegeneratePartition) = [0, 0] := by decide
example : Fintype.card {q : Fin 2 // EdgeNondegenerate
    (nullaryRawWord compositionInner zeroEmptyWord 1 nullaryDegeneratePartition) q} = 0 :=
  by decide

-- 反復する色への空語代入は実際の合成射で零。
example : ((complexPartialComposition ℤ 1 0 0 ▷ interval ℤ) ≫ cochainAction ℤ 1).f (-2)
    (wordPairEdgeInput ℤ compositionInner zeroEmptyWord) = 0 :=
  cochainAction_composition_basis_edge_nullary_of_count_ne_one ℤ compositionInner zeroEmptyWord 0
    (by decide)

-- 出力 arity 零も含む合成則を任意の整数次数・任意の元で使える。
example (z : ℤ) (x : ((complex ℤ 1 ⊗ complex ℤ 0) ⊗ interval ℤ).X z) :
    ((complexPartialComposition ℤ 0 0 0 ▷ interval ℤ) ≫ cochainAction ℤ 0).f z x =
      (iteratedCochainAction ℤ 0 0 0).f z x :=
  congrArg (fun f => f.f z x) (cochainAction_comp ℤ 0 0 0)
example : (barrattEcclesCoalgebra ℤ).carrier = interval ℤ := rfl

-- 実際の正規化区間で、整数線形結合の収縮値とホモトピー値を確認する。
example : contractionHomotopyComponent ℤ 0 (-1)
    ((3 : ℤ) • (show (interval ℤ).X 0 from faceVector ℤ (vertex 1)) -
      (2 : ℤ) • (show (interval ℤ).X 0 from faceVector ℤ (vertex 0))) =
      (3 : ℤ) • faceVector ℤ edge := by
  rw [map_sub, map_zsmul, map_zsmul, contractionHomotopyComponent_vertex,
    contractionHomotopyComponent_vertex]
  change (3 : ℤ) • (show (interval ℤ).X (-1) from faceVector ℤ edge) -
    (2 : ℤ) • (0 : (interval ℤ).X (-1)) = (3 : ℤ) • faceVector ℤ edge
  simp only [zsmul_zero, sub_zero]
example : (contraction ℤ).f 0
    ((3 : ℤ) • (show (interval ℤ).X 0 from faceVector ℤ (vertex 1)) -
      (2 : ℤ) • (show (interval ℤ).X 0 from faceVector ℤ (vertex 0))) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat ℤ))).inv (1 : ℤ) := by
  rw [map_sub, map_zsmul, map_zsmul, contraction_vertex_eq, contraction_vertex_eq,
    sub_eq_add_neg, ← sub_zsmul]
  exact one_zsmul _
example : endpoint ℤ true ≫ contraction ℤ = 𝟙 _ := endpoint_contraction ℤ true
example : QuasiIso (endpoint ℤ true) := endpoint_quasiIso ℤ true
example : QuasiIso (contraction ℤ) := contraction_quasiIso ℤ

-- 区間射の普遍構成で、両頂点を交換し辺の向きを反転する鎖射を作る。
noncomputable section
private def reverseIntervalVertices (c : Fin 2) : (interval ℤ).X 0 :=
  if c = 0 then faceVector ℤ (vertex 1) else faceVector ℤ (vertex 0)
private lemma reverseIntervalVertices_closed (c : Fin 2) :
    (interval ℤ).d 0 1 (reverseIntervalVertices c) = 0 := by
  by_cases hc : c = 0
  · simp only [reverseIntervalVertices, ite_eq_left hc]
    exact faceVector_vertex_d ℤ 1
  · simp only [reverseIntervalVertices, ite_eq_right hc]
    exact faceVector_vertex_d ℤ 0
private lemma reverseIntervalEdge_boundary :
    (interval ℤ).d (-1) 0 (-(show (interval ℤ).X (-1) from faceVector ℤ edge)) =
      reverseIntervalVertices 1 - reverseIntervalVertices 0 := by
  rw [map_neg, faceVector_edge_d_sub]
  change -((show (interval ℤ).X 0 from faceVector ℤ (vertex 1)) -
    (show (interval ℤ).X 0 from faceVector ℤ (vertex 0))) = _
  exact neg_sub _ _
private def reverseInterval : interval ℤ ⟶ interval ℤ :=
  intervalMap ℤ (interval ℤ) reverseIntervalVertices
    (-(show (interval ℤ).X (-1) from faceVector ℤ edge)) reverseIntervalVertices_closed
    reverseIntervalEdge_boundary
private lemma reverseInterval_zero : reverseInterval.f 0 (faceVector ℤ (vertex 0)) =
    faceVector ℤ (vertex 1) :=
  intervalMap_vertex ℤ _ _ _ _ _ 0
private lemma reverseInterval_one : reverseInterval.f 0 (faceVector ℤ (vertex 1)) =
    faceVector ℤ (vertex 0) :=
  intervalMap_vertex ℤ _ _ _ _ _ 1
private lemma reverseInterval_edge : reverseInterval.f (-1) (faceVector ℤ edge) =
    -(show (interval ℤ).X (-1) from faceVector ℤ edge) :=
  intervalMap_edge ℤ _ _ _ _ _
example : reverseInterval ≫ reverseInterval = 𝟙 (interval ℤ) := by
  apply interval_hom_ext ℤ
  · intro c
    fin_cases c
    · exact (congrArg (fun x : (interval ℤ).X 0 => reverseInterval.f 0 x)
        reverseInterval_zero).trans reverseInterval_one
    · exact (congrArg (fun x : (interval ℤ).X 0 => reverseInterval.f 0 x)
        reverseInterval_one).trans reverseInterval_zero
  · change reverseInterval.f (-1) (reverseInterval.f (-1) (faceVector ℤ edge)) =
      faceVector ℤ edge
    rw [reverseInterval_edge, map_neg, reverseInterval_edge, neg_neg]

-- 境界包含の型は生成類の左持ち上げ性そのもので、モデル構造の仮定は要らない。
example : (SerrePositivity.EInfinity.projectiveGeneratingCofibrations ℤ).rlp.llp
    (CategoryTheory.Limits.biprod.desc (endpoint ℤ false) (endpoint ℤ true)) :=
  boundary_cofibration ℤ

-- 具体区間とモデル構造は任意の可換環上で追加仮定なしに利用できる。
example (A : Type) [CommRing A] :
    (coalgebraInterval A).coalgebra.carrier = interval A := rfl
example (A : Type) [CommRing A] :
    HomotopicalAlgebra.ModelCategory
      (SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  SerrePositivity.EInfinity.BarrattEccles.modelCategory A
example (A : Type) [CommRing A] :
    let := SerrePositivity.EInfinity.projectiveModelCategory A
    let := SerrePositivity.EInfinity.BarrattEccles.modelCategory A
    SerrePositivity.Quillen.IsRightQuillen
      (SerrePositivity.EInfinity.Operad.Algebra.forget
        (SerrePositivity.EInfinity.BarrattEccles.operad A)) :=
  SerrePositivity.EInfinity.BarrattEccles.forget_isRightQuillen A

-- nullary も含む零次係数の和を、TR 制限と実際の端点の余作用に使える。
example : SerrePositivity.EInfinity.Surjection.zeroAugmentation ℤ 0
    ((3 : ℤ) • listGenerator ℤ (n := 0) (d := 0) [] -
      (2 : ℤ) • listGenerator ℤ (n := 0) (d := 0) []) = 1 := by
  rw [map_sub, map_zsmul, map_zsmul,
    SerrePositivity.EInfinity.Surjection.zeroAugmentation_empty]
  decide

-- fibrancy は対象にも基礎環にも追加の仮定を課さない。
example (A : Type) [CommRing A]
    (X : (SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    let := SerrePositivity.EInfinity.BarrattEccles.modelCategory A
    HomotopicalAlgebra.IsFibrant X :=
  SerrePositivity.EInfinity.BarrattEccles.isFibrant A X

-- 任意の可換環上の任意の cospan で、同じ置換を底の複体の引き戻しに使える。
open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type) [CommRing A] {X Y Z : (BarrattEccles.operad A).Algebra}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    (homotopyPullback A f g).carrier ≅
      CategoryTheory.Limits.pullback (fibrationReplacement A f).p.hom g.hom :=
  homotopyPullbackCarrierIso A f g

-- 値の局所化に標準の局所化を取っても、導来引き戻しの存在に追加仮定は要らない。
open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type) [CommRing A] {Y Z : (BarrattEccles.operad A).Algebra} (g : Y ⟶ Z) :
    let := modelCategory A
    (pullbackFunctor A g ⋙
      (HomotopicalAlgebra.weakEquivalences
        (BarrattEccles.operad A).Algebra).Q).HasPointwiseRightDerivedFunctor
      (HomotopicalAlgebra.weakEquivalences (Over Z)) := by
  let := modelCategory A
  change (pullbackFunctor A g ⋙ _).HasPointwiseRightDerivedFunctor _
  exact pullbackFunctor_hasPointwiseRightDerivedFunctor A g _ inferInstance

-- 通常の可換代数は、実際に元の加群の零次複体を持つ E 代数になる。
open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type) [CommRing A] (B : CommAlgCat A) :
    ((discreteAlgebraFunctor A).obj B).carrier =
      SerrePositivity.cochainSingleZero (ModuleCat.of A B) :=
  discreteAlgebraFunctor_carrier A B

-- 元の積を保持しており、同じ環上の任意の元で計算できる。
example (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (x y : B) :
    @CategoryTheory.MonObj.mul (ModuleCat A) _ _ _
      (SerrePositivity.EInfinity.moduleCommMonoid A B).mon (x ⊗ₜ[A] y) = x * y := rfl

-- E 代数射を忘却して零次を評価すると、元の代数射の値そのものになる。
open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type) [CommRing A] {B D : CommAlgCat A} (f : B ⟶ D) (x : B) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A D)).hom
      (((discreteAlgebraFunctor A).map f).hom.f 0
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A B)).inv x)) =
      f.hom x := by
  rw [discreteAlgebraFunctor_map, HomologicalComplex.single_map_f_self]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A D)).hom
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A D)).inv
      (f.hom ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A B)).hom
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A B)).inv x)))) = _
  exact (ModuleCat.hom_inv_apply
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A D)) _).trans
    (congrArg (fun b : B => f.hom b) (ModuleCat.hom_inv_apply
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A B)) x))

-- 実際の正規化区間では、辺の境界である二頂点の差は H⁰ で消える。
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.HomologyZero
private def intervalVertexCycle (b : Fin 2) : zeroCycles (interval ℤ) :=
  ⟨faceVector ℤ (vertex b), faceVector_vertex_d ℤ b⟩
example : classMap (interval ℤ) (intervalVertexCycle 1) =
    classMap (interval ℤ) (intervalVertexCycle 0) := by
  rw [← sub_eq_zero, ← map_sub]
  apply (classMap_eq_zero_iff (interval ℤ) _).mpr
  exact ⟨faceVector ℤ edge, faceVector_edge_d_sub ℤ⟩

-- 単位の一の類は消えておらず、実際の H⁰ の型を使っている。
example : unitClass (𝟙_ (SerrePositivity.DifferentialGraded.Complex ℤ)) (𝟙 _) ≠ 0 := by
  intro h
  obtain ⟨x, hx⟩ := (classMap_eq_zero_iff _ _).mp h
  change (0 : ℤ) = 1 at hx
  norm_num at hx

-- E 代数の H⁰ の積は元の加群構造について双線形である。
open SerrePositivity.EInfinity.BarrattEccles in
example (X : (BarrattEccles.operad ℤ).Algebra) (a b c : X.carrier.homology 0) :
    homologyProduct X ((3 : ℤ) • a + b) c =
      (3 : ℤ) • homologyProduct X a c + homologyProduct X b c := by
  rw [map_add, map_zsmul]
  rfl


-- H⁰ の局所的な環構造で二項展開を計算でき、積は元の演算と一致する。
open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type) [CommRing A] (X : (BarrattEccles.operad A).Algebra)
    (x y : X.carrier.homology 0) :
    let := homologyCommRing X
    (x + y) * (x + y) = homologyProduct X x x +
      (2 : X.carrier.homology 0) * homologyProduct X x y + homologyProduct X y y := by
  let := homologyCommRing X
  change (x + y) * (x + y) = x * x + 2 * (x * y) + y * y
  ring

-- 基礎環の像による積は、元のホモロジー加群のスカラー作用そのものである。
open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type) [CommRing A] (X : (BarrattEccles.operad A).Algebra)
    (a : A) (x : X.carrier.homology 0) :
    let := homologyCommRing X
    let := homologyAlgebra X
    homologyProduct X (a • homologyOne X) x = a • x := by
  let := homologyCommRing X
  let := homologyAlgebra X
  change (a • (1 : X.carrier.homology 0)) * x = a • x
  rw [smul_mul_assoc, one_mul]


-- 無限積の比較は元の射影を保つ。
open CategoryTheory.Limits SerrePositivity.EInfinity.BarrattEccles in
example (X : ℕ → (BarrattEccles.operad ℤ).Algebra) (n : ℕ) :
    (productCarrierIso ℤ ℕ X).hom ≫ Pi.π (fun i => (X i).carrier) n =
      (Pi.π X n).hom := by
  exact piComparison_comp_π (Operad.Algebra.forget (BarrattEccles.operad ℤ)) X n

-- 可算個の擬同型の積も元の複体で擬同型であり、モデル構造の入力は要らない。
open SerrePositivity.EInfinity.BarrattEccles in
example {F G : Discrete ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (f : F ⟶ G)
    (hf : ∀ k, QuasiIso (f.app k).hom) :
    QuasiIso (((productFunctor ℤ ℕ).map f).hom) := by
  exact (BarrattEccles.weakEquivalence_iff ℤ _).mp
    (product_map_weakEquivalence ℤ ℕ f hf)

-- 非離散な塔の元の射についても、具体的な局所化との比較は自然。
open SerrePositivity.EInfinity.BarrattEccles in
example {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (f : F ⟶ G) :
    let W := Diagram.objectwiseQuasiIsos ℤ ℕ
    let U := Diagram.forget ℤ ℕ
    let Q := W.Q
    let L := (W.inverseImage U).Q
    Q.map (U.map f) ≫ (Diagram.localizedForgetComparison ℤ ℕ Q L).hom.app G =
      (Diagram.localizedForgetComparison ℤ ℕ Q L).hom.app F ≫
        (Diagram.localizedForget ℤ ℕ Q L).map (L.map f) := by
  let W := Diagram.objectwiseQuasiIsos ℤ ℕ
  let U := Diagram.forget ℤ ℕ
  let Q := W.Q
  let L := (W.inverseImage U).Q
  exact (Diagram.localizedForgetComparison ℤ ℕ Q L).hom.naturality f


-- どの境界制限も、元の E 代数の全整数次数で全射である。
open SerrePositivity.EInfinity.BarrattEccles in
example (X : (BarrattEccles.operad ℤ).Algebra) (n : ℕ) (q : ℤ) :
    Function.Surjective
      ((((cotensor ℤ X).map (SSet.boundary n).ι.op).hom).f q) := by
  have h := cotensor_map_fibration ℤ X (SSet.boundary n).ι inferInstance
  exact (BarrattEccles.fibration_iff ℤ _).mp h q

-- 全次元のホーン制限は、元の底の複体で擬同型となる。
open SerrePositivity.EInfinity.BarrattEccles in
example (X : (BarrattEccles.operad ℤ).Algebra) (n : ℕ) (i : Fin (n + 2)) :
    QuasiIso (((cotensor ℤ X).map (SSet.horn (n + 1) i).ι.op).hom) := by
  exact (cotensor_map_trivialFibration ℤ X (SSet.horn (n + 1) i).ι
    (SSet.anodyneExtensions.horn_ι i)).2

-- 非離散な小図式の重み付き end への射は、全単体の成分で決まる。
open SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) (W : ℕ ⥤ SSet)
    (Y : (BarrattEccles.operad ℤ).Algebra)
    (f g : Y ⟶ (weightedCotensor ℤ ℕ F).obj (Opposite.op W))
    (h : ∀ (k : ℕᵒᵖᵒᵖ) (n : SimplexCategoryᵒᵖ),
      (((weightedCotensorHomEquiv ℤ ℕ F W Y) f).app k).app n =
        (((weightedCotensorHomEquiv ℤ ℕ F W Y) g).app k).app n) : f = g := by
  apply (weightedCotensorHomEquiv ℤ ℕ F W Y).injective
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  exact h k n

-- 図式モデルから構成した実際の Map^h は、元の両図式に条件を置かず全ホーンを充填する。
open SerrePositivity.EInfinity.BarrattEccles in
example (F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) (n : ℕ) (i : Fin (n + 2))
    (a : (SSet.horn (n + 1) i : SSet) ⟶
      ((Diagram.mappingSpace ℤ ℕ).obj (Opposite.op F)).obj G) :
    ∃ b : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶
      ((Diagram.mappingSpace ℤ ℕ).obj (Opposite.op F)).obj G,
      a = (SSet.horn (n + 1) i).ι ≫ b := by
  have := Diagram.mappingSpace_kanComplex ℤ ℕ (Opposite.op F) G
  exact SSet.KanComplex.hornFilling a

-- 元の定値図式の射の合成を、始域 frame の錐の実際の連結成分で回収する。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra)
    {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra}
    (f : (Functor.const ℕ).obj Y ⟶ F) (g : F ⟶ G) :
    SSet.mapπ₀ ((constantDiagramSourceHom ℤ ℕ Y).map g) (constantDiagramSourceClass ℤ ℕ f) =
      constantDiagramSourceClass ℤ ℕ (f ≫ g) := by
  let := Diagram.projectiveModelCategory ℤ ℕ
  let Q := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
  apply (constantDiagramSourcePiZeroEquiv ℤ ℕ Y G).injective
  rw [constantDiagramSourcePiZeroEquiv_target, constantDiagramSourcePiZeroEquiv_class,
    constantDiagramSourcePiZeroEquiv_class]
  exact (Q.map_comp f g).symm

-- 局所化後の任意の射は、構成した Kan 錐の実際の零単体で表せる。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) :
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    ∀ h : Q.obj ((Functor.const ℕ).obj Y) ⟶ Q.obj F,
      ∃ z : ((constantDiagramSourceHom ℤ ℕ Y).obj F).obj (Opposite.op (SimplexCategory.mk 0)),
        constantDiagramSourcePiZeroEquiv ℤ ℕ Y F (SSet.π₀.mk z) = h := by
  let := Diagram.projectiveModelCategory ℤ ℕ
  dsimp only
  intro h
  let e := constantDiagramSourcePiZeroEquiv ℤ ℕ Y F
  obtain ⟨c, hc⟩ := e.surjective h
  obtain ⟨z, hz⟩ := SSet.π₀.mk_surjective c
  exact ⟨z, (congrArg e hz).trans hc⟩

-- Map^h から重み付き錐への比較は、反転後も元の終域図式の射に自然。
open SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra)
    {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (g : F ⟶ G)
    (z : SSet.π₀ (((Diagram.mappingSpace ℤ ℕ).obj
      (Opposite.op ((Functor.const ℕ).obj Y))).obj F)) :
    let e := constantDiagramSourceMappingComparisonIso ℤ ℕ SSet.π₀Functor
      SerrePositivity.SimplicialModel.PiZeroLocalization.inverts_anodyne Y
    e.hom.app G (SSet.mapπ₀ (((Diagram.mappingSpace ℤ ℕ).obj
      (Opposite.op ((Functor.const ℕ).obj Y))).map g) z) =
      SSet.mapπ₀ ((constantDiagramSourceHom ℤ ℕ Y).map g) (e.hom.app F z) := by
  let e := constantDiagramSourceMappingComparisonIso ℤ ℕ SSet.π₀Functor
    SerrePositivity.SimplicialModel.PiZeroLocalization.inverts_anodyne Y
  exact ConcreteCategory.congr_hom (e.hom.naturality g) z


-- 選んだ重みの各値への任意の部分写像は、すべての単射に沿って延長できる。
open SerrePositivity.EInfinity.HomotopyWeight in
example (k : ℕ) {X Y : SSet} (i : X ⟶ Y) [Mono i]
    (a : X ⟶ (weight ℕ).obj k) : ∃ b : Y ⟶ (weight ℕ).obj k, i ≫ b = a := by
  have : HasLiftingProperty i ((comparison ℕ).app k) := comparison_mono_rlp ℕ k i inferInstance
  let sq : CommSq a i ((comparison ℕ).app k) (CategoryTheory.Limits.terminal.from Y) :=
    ⟨CategoryTheory.Limits.terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

-- 空図式の実際の計算対象は終対象であり、空の homotopy 極限の値を回収する。
open CategoryTheory.Limits SerrePositivity.EInfinity.BarrattEccles in
example (F : PEmpty ⥤ (BarrattEccles.operad ℤ).Algebra) :
    IsTerminal ((framedLimitFunctor ℤ PEmpty).obj F) := by
  let a (Y : (BarrattEccles.operad ℤ).Algebra) :
      (doubleOpWeights PEmpty).obj (HomotopyWeight.weight PEmpty) ⟶
        (SerrePositivity.DiagramModel.FrameWeightRealization.hom PEmptyᵒᵖ
          (rightFrameDiagram ℤ PEmpty F)).obj (Opposite.op Y) :=
    { app k := PEmpty.elim k.unop.unop
      naturality := by intro k l f; cases k.unop.unop }
  refine IsTerminal.ofUniqueHom
    (fun Y => (weightedCotensorHomEquiv ℤ PEmpty F (HomotopyWeight.weight PEmpty) Y).symm
      (a Y)) ?_
  intro Y m
  apply (weightedCotensorHomEquiv ℤ PEmpty F (HomotopyWeight.weight PEmpty) Y).injective
  apply NatTrans.ext
  funext k
  exact PEmpty.elim k.unop.unop


-- 構成した Map^h は実際の単体集合として全次元のホーンを充填する。
open SerrePositivity.EInfinity.BarrattEccles in
example (X Y : (BarrattEccles.operad ℤ).Algebra) (n : ℕ) (i : Fin (n + 2))
    (a : (SSet.horn (n + 1) i : SSet) ⟶ ((mappingSpace ℤ).obj (Opposite.op X)).obj Y) :
    ∃ b : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶
      ((mappingSpace ℤ).obj (Opposite.op X)).obj Y, a = (SSet.horn (n + 1) i).ι ≫ b := by
  have := mappingSpace_kanComplex ℤ (Opposite.op X) Y
  exact SSet.KanComplex.hornFilling a

-- 元の二つの代数射の合成は、Map^h の実際の π₀ の後合成で回収される。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example {X Y Z : (BarrattEccles.operad ℤ).Algebra} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.mapπ₀ (((mappingSpace ℤ).obj (Opposite.op X)).map g) (mappingSpaceClass ℤ f) =
      mappingSpaceClass ℤ (f ≫ g) := by
  let := BarrattEccles.modelCategory ℤ
  let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
  apply (mappingSpacePiZeroEquiv ℤ Q (Opposite.op X) Z).injective
  rw [mappingSpacePiZeroEquiv_target, mappingSpacePiZeroEquiv_class,
    mappingSpacePiZeroEquiv_class]
  exact (Q.map_comp f g).symm

-- 元の擬同型の導来的な逆は、逆向きの実際の写像空間の連結成分で表せる。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example {X Y : (BarrattEccles.operad ℤ).Algebra} (f : X ⟶ Y) (hf : QuasiIso f.hom) :
    let := BarrattEccles.modelCategory ℤ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    ∃ z : SSet.π₀ (((mappingSpace ℤ).obj (Opposite.op Y)).obj X),
      Q.map f ≫ mappingSpacePiZeroEquiv ℤ Q (Opposite.op Y) X z = 𝟙 _ ∧
        mappingSpacePiZeroEquiv ℤ Q (Opposite.op Y) X z ≫ Q.map f = 𝟙 _ := by
  let := BarrattEccles.modelCategory ℤ
  let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
  have : IsIso (Q.map f) := Localization.inverts Q
    (weakEquivalences (BarrattEccles.operad ℤ).Algebra) f hf
  let e := mappingSpacePiZeroEquiv ℤ Q (Opposite.op Y) X
  refine ⟨e.symm (inv (Q.map f)), ?_, ?_⟩
  · change Q.map f ≫ e (e.symm (inv (Q.map f))) = 𝟙 _
    rw [e.apply_symm_apply, IsIso.hom_inv_id]
  · change e (e.symm (inv (Q.map f))) ≫ Q.map f = 𝟙 _
    rw [e.apply_symm_apply, IsIso.inv_hom_id]

-- 選んだ射影重みの錐は頂点ごとに充填するだけでなく、図式全体に自然な充填を持つ。
open CategoryTheory.Limits SerrePositivity.EInfinity.HomotopyWeight
  SerrePositivity.DiagramModel.WeightedCones in
example {F G : ℕ ⥤ SSet} (p : F ⟶ G)
    (hp : ∀ k, SSet.modelCategoryQuillen.I.rlp (p.app k))
    {X Y : SSet} (i : X ⟶ Y) [Mono i]
    (a : X ⟶ (coneSpace ℕ (weight ℕ)).obj F)
    (b : Y ⟶ (coneSpace ℕ (weight ℕ)).obj G)
    (h : a ≫ (coneSpace ℕ (weight ℕ)).map p = i ≫ b) :
    ∃ l : Y ⟶ (coneSpace ℕ (weight ℕ)).obj F,
      i ≫ l = a ∧ l ≫ (coneSpace ℕ (weight ℕ)).map p = b := by
  have : HasLiftingProperty i ((coneSpace ℕ (weight ℕ)).map p) :=
    SSet.rlp_monomorphisms.ge _
      (coneSpace_map_boundary_rlp ℕ (weight ℕ) (weight_cofibrant ℕ) p hp) i inferInstance
  let sq : CommSq a i ((coneSpace ℕ (weight ℕ)).map p) b := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

-- Kan 値図式の実際の重み付き錐空間は全次元のホーンを充填する。
open SerrePositivity.EInfinity.HomotopyWeight
  SerrePositivity.DiagramModel.WeightedCones in
example (F : ℕ ⥤ SSet) (hF : ∀ k, SSet.KanComplex (F.obj k))
    (n : ℕ) (i : Fin (n + 2))
    (a : (SSet.horn (n + 1) i : SSet) ⟶ (coneSpace ℕ (weight ℕ)).obj F) :
    ∃ b : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶
      (coneSpace ℕ (weight ℕ)).obj F, a = (SSet.horn (n + 1) i).ι ≫ b := by
  have := coneSpace_kanComplex ℕ (weight ℕ) (weight_cofibrant ℕ) F hF
  exact SSet.KanComplex.hornFilling a

-- 元の E 代数に cofibrancy を仮定せず、右 frame の錐の全次元のホーンを充填する。
open SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (Y : (BarrattEccles.operad ℤ).Algebra) (n : ℕ) (i : Fin (n + 2))
    (a : (SSet.horn (n + 1) i : SSet) ⟶ (framedLimitConeSpace ℤ ℕ Y).obj F) :
    ∃ b : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶
      (framedLimitConeSpace ℤ ℕ Y).obj F, a = (SSet.horn (n + 1) i).ι ≫ b := by
  have := framedLimitConeSpace_kanComplex ℤ ℕ F Y
  exact SSet.KanComplex.hornFilling a

-- 頂点ごとの代数の擬同型を通して、各連結成分の錐は一意な成分へ戻せる。
open SerrePositivity.EInfinity.BarrattEccles in
example {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (f : F ⟶ G)
    (hf : ∀ k, QuasiIso (f.app k).hom) (Y : (BarrattEccles.operad ℤ).Algebra)
    (z : SSet.π₀ ((framedLimitConeSpace ℤ ℕ Y).obj G)) :
    ∃! w : SSet.π₀ ((framedLimitConeSpace ℤ ℕ Y).obj F),
      SSet.mapπ₀ ((framedLimitConeSpace ℤ ℕ Y).map f) w = z := by
  obtain ⟨hinj, hsurj⟩ := framedLimitConeSpace_map_piZero_bijective ℤ ℕ f hf Y
  obtain ⟨w, hw⟩ := hsurj z
  exact ⟨w, hw, fun w' hw' => hinj (hw'.trans hw.symm)⟩

-- 実際の計算対象の擬同型は、同じ底の重み付き end の比較同型を通しても擬同型。
open SerrePositivity.EInfinity.BarrattEccles in
example {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (f : F ⟶ G)
    (hf : ∀ k, QuasiIso (f.app k).hom) :
    QuasiIso ((framedLimitCarrierIso ℤ ℕ F).inv ≫
      ((framedLimitFunctor ℤ ℕ).map f).hom ≫ (framedLimitCarrierIso ℤ ℕ G).hom) := by
  have := framedLimitFunctor_map_quasiIso ℤ ℕ f hf
  infer_instance

-- 元の図式の頂点ごとの擬同型は、計算対象の局所化後の実際の二側逆を持つ。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (f : F ⟶ G)
    (hf : ∀ k, QuasiIso (f.app k).hom) :
    let := BarrattEccles.modelCategory ℤ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    ∃ g : Q.obj ((framedLimitFunctor ℤ ℕ).obj G) ⟶
        Q.obj ((framedLimitFunctor ℤ ℕ).obj F),
      Q.map ((framedLimitFunctor ℤ ℕ).map f) ≫ g = 𝟙 _ ∧
        g ≫ Q.map ((framedLimitFunctor ℤ ℕ).map f) = 𝟙 _ := by
  let := BarrattEccles.modelCategory ℤ
  let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
  have : IsIso (Q.map ((framedLimitFunctor ℤ ℕ).map f)) :=
    Localization.inverts Q (weakEquivalences (BarrattEccles.operad ℤ).Algebra) _
      (framedLimitFunctor_map_quasiIso ℤ ℕ f hf)
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

-- 定値図式の具体的な置換は、図式全体で自明 fibration に沿って持ち上がる。
open CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra)
    {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (p : F ⟶ G)
    (hp : ∀ k n, Function.Surjective ((p.app k).hom.f n))
    (hq : ∀ k, QuasiIso (p.app k).hom)
    (b : (constantDiagramReplacement ℤ ℕ).obj Y ⟶ G) :
    ∃ l : (constantDiagramReplacement ℤ ℕ).obj Y ⟶ F, l ≫ p = b := by
  let := Diagram.projectiveModelCategory ℤ ℕ
  have := constantDiagramReplacement_isCofibrant ℤ ℕ Y
  have : Fibration p := (Diagram.fibration_iff ℤ ℕ p).mpr hp
  have : WeakEquivalence p := (Diagram.weakEquivalence_iff ℤ ℕ p).mpr hq
  let sq : CommSq (initial.to F)
      (initial.to ((constantDiagramReplacement ℤ ℕ).obj Y)) p b := ⟨initial.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_right⟩

-- 置換からの実際の図式射は、随伴の錐の全成分で判定できる。
open SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (f g : (constantDiagramReplacement ℤ ℕ).obj Y ⟶ F)
    (h : let := BarrattEccles.modelCategory ℤ
      ∀ k n, (((constantDiagramHomEquiv ℤ ℕ Y F) f).app k).app n =
        (((constantDiagramHomEquiv ℤ ℕ Y F) g).app k).app n) : f = g := by
  let := BarrattEccles.modelCategory ℤ
  apply (constantDiagramHomEquiv ℤ ℕ Y F).injective
  apply NatTrans.ext
  funext k
  apply NatTrans.ext
  funext n
  exact h k n

-- Kan 値図式の各値の局所化同値は、同じ錐の連結成分を一意に戻す。
open SerrePositivity.EInfinity.HomotopyWeight
  SerrePositivity.DiagramModel.WeightedCones SerrePositivity.SimplicialModel in
example {F G : ℕ ⥤ SSet} (f : F ⟶ G)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    (z : SSet.π₀ ((coneSpace ℕ (weight ℕ)).obj G)) :
    ∃! w : SSet.π₀ ((coneSpace ℕ (weight ℕ)).obj F),
      SSet.mapπ₀ ((coneSpace ℕ (weight ℕ)).map f) w = z := by
  have := coneSpace_map_isIso_of_pointwiseKan ℕ (weight ℕ) (weight_cofibrant ℕ)
    f hF hG hf SSet.π₀Functor PiZeroLocalization.inverts_anodyne
  obtain ⟨hinj, hsurj⟩ := (CategoryTheory.isIso_iff_bijective _).mp this
  obtain ⟨w, hw⟩ := hsurj z
  exact ⟨w, hw, fun w' hw' => hinj (hw'.trans hw.symm)⟩

-- 共通図式は Kan でなくても、元の二つの比較射の像は同じ類になる。
open CategoryTheory.Limits SerrePositivity.EInfinity.HomotopyWeight
  SerrePositivity.DiagramModel.WeightedCones SerrePositivity.SimplicialModel in
example {F G H : ℕ ⥤ SSet} (f : F ⟶ H) (g : G ⟶ H)
    (hF : ∀ k, SSet.KanComplex (F.obj k)) (hG : ∀ k, SSet.KanComplex (G.obj k))
    (hf : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (f.app k)))
    (hg : ∀ k, IsIso (AnodyneHomotopy.anodyneQ.map (g.app k)))
    (z : SSet.π₀ ((coneSpace ℕ (weight ℕ)).obj F)) :
    let e := kanConeComparisonIso ℕ (weight ℕ) (weight_cofibrant ℕ)
      SSet.π₀Functor PiZeroLocalization.inverts_anodyne f g hF hG hf hg
    (coneComparisonArrow ℕ (weight ℕ) SSet.π₀Functor g) (e.hom z) =
      (coneComparisonArrow ℕ (weight ℕ) SSet.π₀Functor f) z := by
  exact ConcreteCategory.congr_hom
    (kanConeComparisonIso_fac ℕ (weight ℕ) (weight_cofibrant ℕ)
      SSet.π₀Functor PiZeroLocalization.inverts_anodyne f g hF hG hf hg) z

-- 元の定値図式の局所化射は、計算した同じ極限対象への射で一意に表せる。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (f : (CategoryTheory.Functor.const ℕ).obj Y ⟶ F) :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    ∃! g : Q.obj Y ⟶ Q.obj ((framedLimitFunctor ℤ ℕ).obj F),
      (framedLimitDerivedHomEquiv ℤ ℕ Y F).symm g = QD.map f := by
  let := BarrattEccles.modelCategory ℤ
  let := Diagram.projectiveModelCategory ℤ ℕ
  dsimp only
  let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
  let e := framedLimitDerivedHomEquiv ℤ ℕ Y F
  refine ⟨e (QD.map f), e.symm_apply_apply _, ?_⟩
  intro g hg
  exact (e.apply_symm_apply g).symm.trans (congrArg e hg)

-- 右 frame の同じ錐は元の図式射の後合成を正しい局所化像へ送る。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra)
    {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (g : F ⟶ G)
    (z : SSet.π₀ ((framedLimitConeSpace ℤ ℕ Y).obj F)) :
    let := Diagram.projectiveModelCategory ℤ ℕ
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    (framedLimitConePiZeroEquiv ℤ ℕ Y G).symm
      (framedLimitConePiZeroEquiv ℤ ℕ Y F z ≫ QD.map g) =
        SSet.mapπ₀ ((framedLimitConeSpace ℤ ℕ Y).map g) z := by
  let := Diagram.projectiveModelCategory ℤ ℕ
  dsimp only
  let e := framedLimitConePiZeroEquiv ℤ ℕ Y G
  exact (congrArg e.symm (framedLimitConePiZeroEquiv_target ℤ ℕ Y g z)).symm.trans
    (e.symm_apply_apply _)

-- 元の錐と図式射の合成は、計算対象への導来射の同じ後合成を回収する。
open HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra)
    {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra}
    (f : (CategoryTheory.Functor.const ℕ).obj Y ⟶ F) (g : F ⟶ G) :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    framedLimitDerivedHomEquiv ℤ ℕ Y G (QD.map (f ≫ g)) =
      framedLimitDerivedHomEquiv ℤ ℕ Y F (QD.map f) ≫ Q.map ((framedLimitFunctor ℤ ℕ).map g) := by
  let := BarrattEccles.modelCategory ℤ
  let := Diagram.projectiveModelCategory ℤ ℕ
  dsimp only
  let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
  exact (congrArg (framedLimitDerivedHomEquiv ℤ ℕ Y G) (QD.map_comp f g)).trans
    (framedLimitDerivedHomEquiv_target ℤ ℕ Y g (QD.map f))

-- 元の始域射・錐・図式射の合成は、導来射の前合成・後合成に一致する。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example {Y Z : (BarrattEccles.operad ℤ).Algebra} (f : Y ⟶ Z)
    {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra}
    (h : (Functor.const ℕ).obj Z ⟶ F) (g : F ⟶ G) :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    framedLimitDerivedHomEquiv ℤ ℕ Y G (QD.map (((Functor.const ℕ).map f ≫ h) ≫ g)) =
      Q.map f ≫ framedLimitDerivedHomEquiv ℤ ℕ Z F (QD.map h) ≫
        Q.map ((framedLimitFunctor ℤ ℕ).map g) := by
  let := BarrattEccles.modelCategory ℤ
  let := Diagram.projectiveModelCategory ℤ ℕ
  dsimp only
  let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
  let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
  have hm : QD.map (((Functor.const ℕ).map f ≫ h) ≫ g) =
      (QD.map ((Functor.const ℕ).map f) ≫ QD.map h) ≫ QD.map g := by
    rw [QD.map_comp, QD.map_comp]
  have hs := framedLimitDerivedHomEquiv_source ℤ ℕ f F (QD.map h)
  have ht := framedLimitDerivedHomEquiv_target ℤ ℕ Y g
    (QD.map ((Functor.const ℕ).map f) ≫ QD.map h)
  have he := (congrArg (framedLimitDerivedHomEquiv ℤ ℕ Y G) hm).trans
    (ht.trans (congrArg (fun x => x ≫ Q.map ((framedLimitFunctor ℤ ℕ).map g)) hs))
  simpa only [Category.assoc] using he

-- 始域の元の射に沿った右錐の前合成は、同じ局所化 Hom の前合成で回収される。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example {Y Z : (BarrattEccles.operad ℤ).Algebra} (f : Y ⟶ Z)
    (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (z : SSet.π₀ ((framedLimitConeSpace ℤ ℕ Z).obj F)) :
    let := Diagram.projectiveModelCategory ℤ ℕ
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    (framedLimitConePiZeroEquiv ℤ ℕ Y F).symm
      (QD.map ((Functor.const ℕ).map f) ≫ framedLimitConePiZeroEquiv ℤ ℕ Z F z) =
        SSet.mapπ₀ ((framedLimitConeSourceMap ℤ ℕ f).app F) z := by
  let := Diagram.projectiveModelCategory ℤ ℕ
  dsimp only
  let e := framedLimitConePiZeroEquiv ℤ ℕ Y F
  exact (congrArg e.symm (framedLimitConePiZeroEquiv_source ℤ ℕ f F z)).symm.trans
    (e.symm_apply_apply _)

-- 元の普通の錐の局所化像を、局所化圏上の随伴の Hom 同値で同じ類へ戻せる。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (Y : (BarrattEccles.operad ℤ).Algebra) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (f : (Functor.const ℕ).obj Y ⟶ F) :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    (framedLimitAdjunction ℤ ℕ).homEquiv (Q.obj Y) (QD.obj F)
        ((localizedConstantDiagramComparison ℤ ℕ).hom.app Y ≫ QD.map f) ≫
      (localizedFramedLimitComparison ℤ ℕ).hom.app F =
        framedLimitDerivedHomEquiv ℤ ℕ Y F (QD.map f) := by
  let := BarrattEccles.modelCategory ℤ
  let := Diagram.projectiveModelCategory ℤ ℕ
  let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
  exact framedLimitAdjunction_homEquiv_comparison ℤ ℕ Y F (QD.map f)

-- 元の対象の像に限らず、局所化圏の任意の二対象で実際の Hom の普遍性を使える。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    ∀ (X : (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Localization)
      (Y : (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Localization)
      (f : X ⟶ (localizedFramedLimit ℤ ℕ).obj Y),
      ∃! g : (localizedConstantDiagram ℤ ℕ).obj X ⟶ Y,
        (framedLimitAdjunction ℤ ℕ).homEquiv X Y g = f := by
  let := BarrattEccles.modelCategory ℤ
  let := Diagram.projectiveModelCategory ℤ ℕ
  dsimp only
  intro X Y f
  let e := (framedLimitAdjunction ℤ ℕ).homEquiv X Y
  refine ⟨e.symm f, e.apply_symm_apply _, ?_⟩
  intro g hg
  exact (e.symm_apply_apply g).symm.trans (congrArg e.symm hg)

-- 元の錐の射で右錐の類を前合成すると、元の同じ錐の普遍射を回収する。
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) {c d : Cone F} (h : c ⟶ d) :
    let := BarrattEccles.modelCategory ℤ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    framedLimitHomPiZeroEquiv ℤ ℕ c.pt F
        (SSet.mapπ₀ ((framedLimitConeSourceMap ℤ ℕ h.hom).app F)
          (framedLimitConeClass ℤ ℕ F d)) = Q.map (coneToFramedLimit ℤ ℕ F c) := by
  let := BarrattEccles.modelCategory ℤ
  dsimp only
  let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
  have hs := framedLimitHomPiZeroEquiv_source ℤ ℕ h.hom F (framedLimitConeClass ℤ ℕ F d)
  have hd := framedLimitHomPiZeroEquiv_coneClass ℤ ℕ F d
  have he := hs.trans (congrArg (fun x => Q.map h.hom ≫ x) hd)
  have hc : Q.map h.hom ≫ Q.map (coneToFramedLimit ℤ ℕ F d) =
      Q.map (coneToFramedLimit ℤ ℕ F c) :=
    (Q.map_comp _ _).symm.trans (congrArg Q.map (coneToFramedLimit_naturality ℤ ℕ F h))
  exact he.trans hc

-- 同じ定値図式比較の随伴族で作る零単体も元の図式射の局所化像となる。
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example {Y : (BarrattEccles.operad ℤ).Algebra} {F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra}
    (f : (Functor.const ℕ).obj Y ⟶ F) :
    let := Diagram.projectiveModelCategory ℤ ℕ
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    constantDiagramSourcePiZeroEquiv ℤ ℕ Y F
        (HomotopyWeight.coneClass ℕ (HomotopyWeight.weight ℕ)
          ((constantDiagramHomEquiv ℤ ℕ Y F) ((constantDiagramComparison ℤ ℕ).app Y ≫ f))) =
      QD.map f := by
  let := Diagram.projectiveModelCategory ℤ ℕ
  exact (congrArg (constantDiagramSourcePiZeroEquiv ℤ ℕ Y F)
    (constantDiagramSourceClass_eq_coneClass ℤ ℕ f)).symm.trans
      (constantDiagramSourcePiZeroEquiv_class ℤ ℕ f)

-- 元の通常錐の比較を、局所化圏全体の随伴の Hom 対応から回収する。
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) (c : Cone F) :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    (framedLimitAdjunction ℤ ℕ).homEquiv (Q.obj c.pt) (QD.obj F)
        ((localizedConstantDiagramComparison ℤ ℕ).hom.app c.pt ≫ QD.map c.π) ≫
      (localizedFramedLimitComparison ℤ ℕ).hom.app F = Q.map (coneToFramedLimit ℤ ℕ F c) := by
  exact framedLimitAdjunction_homEquiv_cone ℤ ℕ F c

-- 通常の極限錐を代入すると、構成済みの同じ limitComparison を得る。
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let QD := (weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)).Q
    framedLimitDerivedHomEquiv ℤ ℕ (limit F) F (QD.map (limit.cone F).π) =
      Q.map (limitComparison ℤ ℕ F) := by
  exact framedLimitDerivedHomEquiv_cone ℤ ℕ F (limit.cone F)

-- 右導来普遍性は任意の候補関手への自然変換の一意な因子化を与える。
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let W := weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    ∀ (T : W.Localization ⥤ (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Localization)
      (β : lim ⋙ Q ⟶ W.Q ⋙ T),
      ∃! γ : localizedFramedLimit ℤ ℕ ⟶ T,
        framedLimitDerivedComparison ℤ ℕ ≫ Functor.whiskerLeft W.Q γ = β := by
  let := BarrattEccles.modelCategory ℤ
  let := Diagram.projectiveModelCategory ℤ ℕ
  have := localizedFramedLimit_isRightDerivedFunctor ℤ ℕ
  dsimp only
  intro T β
  let W := weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
  let RF := localizedFramedLimit ℤ ℕ
  let α := framedLimitDerivedComparison ℤ ℕ
  refine ⟨RF.rightDerivedDesc α W T β, RF.rightDerived_fac α W T β, ?_⟩
  intro γ hγ
  apply RF.rightDerived_ext α W T
  exact hγ.trans (RF.rightDerived_fac α W T β).symm

-- 実際の重み付き end は選択済みの通常右導来関手の値にも同型になる。
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) :
    let := BarrattEccles.modelCategory ℤ
    let := Diagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
    let W := weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    let := limitFunctor_hasRightDerivedFunctor ℤ ℕ
    Q.obj ((framedLimitFunctor ℤ ℕ).obj F) ≅
      ((lim ⋙ Q).totalRightDerived W.Q W).obj (W.Q.obj F) := by
  let := BarrattEccles.modelCategory ℤ
  let := Diagram.projectiveModelCategory ℤ ℕ
  have := limitFunctor_hasRightDerivedFunctor ℤ ℕ
  let Q := (weakEquivalences (BarrattEccles.operad ℤ).Algebra).Q
  let W := weakEquivalences (ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
  exact framedLimitDerivedIso ℤ ℕ F ((lim ⋙ Q).totalRightDerived W.Q W)
    ((lim ⋙ Q).totalRightDerivedUnit W.Q W) inferInstance

-- 元の代数の底とは限らない任意の複体を試験始域に使える。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) (Y : Complex ℤ) :
    SSet.KanComplex ((carrierFramedLimitConeSpace ℤ ℕ Y).obj F) :=
  carrierFramedLimitConeSpace_kanComplex ℤ ℕ F Y

-- 元の通常錐から計算対象への射を忘却した場合にも同じ局所化像になる。
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) (c : Cone F) :
    let := projectiveModelCategory ℤ
    let Q := (weakEquivalences (Complex ℤ)).Q
    carrierFramedLimitHomPiZeroEquiv ℤ ℕ F c.pt.carrier
        (carrierFramedLimitMapClass ℤ ℕ F (coneToFramedLimit ℤ ℕ F c).hom) =
      Q.map (coneToFramedLimit ℤ ℕ F c).hom := by
  exact carrierFramedLimitHomPiZeroEquiv_mapClass ℤ ℕ F (coneToFramedLimit ℤ ℕ F c).hom

-- 任意の複体から計算対象の底への局所化射は、同じ右錐の類で一意に表示される。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) (Y : Complex ℤ) :
    let := projectiveModelCategory ℤ
    let Q := (weakEquivalences (Complex ℤ)).Q
    ∀ x : Q.obj Y ⟶ Q.obj ((framedLimitFunctor ℤ ℕ).obj F).carrier,
      ∃! z, carrierFramedLimitHomPiZeroEquiv ℤ ℕ F Y z = x := by
  let := projectiveModelCategory ℤ
  dsimp only
  intro x
  let e := carrierFramedLimitHomPiZeroEquiv ℤ ℕ F Y
  refine ⟨e.symm x, e.apply_symm_apply _, ?_⟩
  intro z hz
  exact (e.symm_apply_apply z).symm.trans (congrArg e.symm hz)

-- 底の任意の複体図式も実際の射影モデルで fibrant。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ Complex ℤ) :
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    IsFibrant F := CarrierDiagram.isFibrant ℤ ℕ F

-- 元の定値複体図式の射は、錐の類の比較で同じ局所化像になる。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity.BarrattEccles in
example {Y : Complex ℤ} {F : ℕ ⥤ Complex ℤ} (f : (Functor.const ℕ).obj Y ⟶ F) :
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    CarrierDiagram.constantDiagramSourcePiZeroEquiv ℤ ℕ Y F
        (CarrierDiagram.constantDiagramSourceClass ℤ ℕ f) = QD.map f := by
  exact CarrierDiagram.constantDiagramSourcePiZeroEquiv_class ℤ ℕ f

-- 元の図式射による後合成は同じ局所化射の合成と一致する。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity.BarrattEccles in
example {Y : Complex ℤ} {F G : ℕ ⥤ Complex ℤ}
    (f : (Functor.const ℕ).obj Y ⟶ F) (g : F ⟶ G) :
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    CarrierDiagram.constantDiagramSourcePiZeroEquiv ℤ ℕ Y G
        (SSet.mapπ₀ ((CarrierDiagram.constantDiagramSourceHom ℤ ℕ Y).map g)
          (CarrierDiagram.constantDiagramSourceClass ℤ ℕ f)) = QD.map (f ≫ g) := by
  let := CarrierDiagram.projectiveModelCategory ℤ ℕ
  let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
  dsimp only
  rw [CarrierDiagram.constantDiagramSourcePiZeroEquiv_target,
    CarrierDiagram.constantDiagramSourcePiZeroEquiv_class]
  exact (QD.map_comp f g).symm

-- 図式忘却の右 Quillen 性は、両図式モデルの存在を仮定せず使用できる。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity.BarrattEccles in
example :
    let := Diagram.projectiveModelCategory ℤ ℕ
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    SerrePositivity.Quillen.IsRightQuillen (Diagram.forget ℤ ℕ) :=
  Diagram.forget_isRightQuillen ℤ ℕ

-- 底の右錐の π₀ の比較は元の代数図式の射を忘却した後合成に自然。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (Y : Complex ℤ) {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (g : F ⟶ G)
    (z : SSet.π₀ ((carrierFramedLimitConeSpace ℤ ℕ Y).obj F)) :
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    carrierFramedLimitConePiZeroEquiv ℤ ℕ Y G
        (SSet.mapπ₀ ((carrierFramedLimitConeSpace ℤ ℕ Y).map g) z) =
      carrierFramedLimitConePiZeroEquiv ℤ ℕ Y F z ≫ QD.map ((Diagram.forget ℤ ℕ).map g) := by
  exact carrierFramedLimitConePiZeroEquiv_target ℤ ℕ Y g z

-- 底の同じ右錐の類を、二つの局所化 Hom の比較で厳密に回収する。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (Y : Complex ℤ) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (z : SSet.π₀ ((carrierFramedLimitConeSpace ℤ ℕ Y).obj F)) :
    let := projectiveModelCategory ℤ
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    carrierFramedLimitDerivedHomEquiv ℤ ℕ Y F (carrierFramedLimitConePiZeroEquiv ℤ ℕ Y F z) =
      carrierFramedLimitHomPiZeroEquiv ℤ ℕ F Y z := by
  let := projectiveModelCategory ℤ
  let := CarrierDiagram.projectiveModelCategory ℤ ℕ
  change carrierFramedLimitHomPiZeroEquiv ℤ ℕ F Y
    ((carrierFramedLimitConePiZeroEquiv ℤ ℕ Y F).symm
      (carrierFramedLimitConePiZeroEquiv ℤ ℕ Y F z)) = _
  rw [Equiv.symm_apply_apply]

-- 任意の複体から元の計算対象の底への局所化射に、底の定値図式の射が一意に対応。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (Y : Complex ℤ) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) :
    let := projectiveModelCategory ℤ
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (Complex ℤ)).Q
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    ∀ x : Q.obj Y ⟶ Q.obj ((framedLimitFunctor ℤ ℕ).obj F).carrier,
      ∃! y : QD.obj ((Functor.const ℕ).obj Y) ⟶ QD.obj ((Diagram.forget ℤ ℕ).obj F),
        carrierFramedLimitDerivedHomEquiv ℤ ℕ Y F y = x := by
  let := projectiveModelCategory ℤ
  let := CarrierDiagram.projectiveModelCategory ℤ ℕ
  dsimp only
  intro x
  let e := carrierFramedLimitDerivedHomEquiv ℤ ℕ Y F
  refine ⟨e.symm x, e.apply_symm_apply _, ?_⟩
  intro y hy
  exact (e.symm_apply_apply y).symm.trans (congrArg e.symm hy)

-- 元の計算対象の底の同型は実際の図式射に自然。
open CategoryTheory SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (g : F ⟶ G) :
    ((framedLimitFunctor ℤ ℕ).map g).hom ≫ (framedLimitCarrierIso ℤ ℕ G).hom =
      (framedLimitCarrierIso ℤ ℕ F).hom ≫ (carrierFramedLimitFunctor ℤ ℕ).map g := by
  exact framedLimitCarrierIso_naturality ℤ ℕ g

-- 底の導来 Hom 同値は元の忘却図式の局所化射による後合成に自然。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (Y : Complex ℤ) {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (g : F ⟶ G) :
    let := projectiveModelCategory ℤ
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (Complex ℤ)).Q
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    ∀ x : QD.obj ((Functor.const ℕ).obj Y) ⟶ QD.obj ((Diagram.forget ℤ ℕ).obj F),
      carrierFramedLimitDerivedHomEquiv ℤ ℕ Y G (x ≫ QD.map ((Diagram.forget ℤ ℕ).map g)) =
        carrierFramedLimitDerivedHomEquiv ℤ ℕ Y F x ≫ Q.map ((framedLimitFunctor ℤ ℕ).map g).hom := by
  exact carrierFramedLimitDerivedHomEquiv_target ℤ ℕ Y g

-- 元の複体射のクラスを図式射で送ると、元の複体射の後合成の局所化像になる。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example {Y : Complex ℤ} {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (g : F ⟶ G)
    (h : Y ⟶ ((framedLimitFunctor ℤ ℕ).obj F).carrier) :
    let := projectiveModelCategory ℤ
    let Q := (weakEquivalences (Complex ℤ)).Q
    carrierFramedLimitHomPiZeroEquiv ℤ ℕ G Y
        (SSet.mapπ₀ ((carrierFramedLimitConeSpace ℤ ℕ Y).map g)
          (carrierFramedLimitMapClass ℤ ℕ F h)) = Q.map (h ≫ ((framedLimitFunctor ℤ ℕ).map g).hom) := by
  let := projectiveModelCategory ℤ
  let Q := (weakEquivalences (Complex ℤ)).Q
  dsimp only
  rw [carrierFramedLimitHomPiZeroEquiv_target, carrierFramedLimitHomPiZeroEquiv_mapClass]
  exact (Q.map_comp _ _).symm

-- 任意の元の複体射の前合成は、実際の計算対象の底への同じ射の局所化になる。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example {Y Z : Complex ℤ} (f : Y ⟶ Z) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (h : Z ⟶ ((framedLimitFunctor ℤ ℕ).obj F).carrier) :
    let := projectiveModelCategory ℤ
    let Q := (weakEquivalences (Complex ℤ)).Q
    carrierFramedLimitHomPiZeroEquiv ℤ ℕ F Y
        (SSet.mapπ₀ ((carrierFramedLimitConeSourceMap ℤ ℕ f).app F)
          (carrierFramedLimitMapClass ℤ ℕ F h)) = Q.map (f ≫ h) := by
  let := projectiveModelCategory ℤ
  let Q := (weakEquivalences (Complex ℤ)).Q
  dsimp only
  rw [carrierFramedLimitHomPiZeroEquiv_source, carrierFramedLimitHomPiZeroEquiv_mapClass]
  exact (Q.map_comp _ _).symm

-- 底の同じ右錐の類の前合成は、元の定値複体図式の局所化射による前合成。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example {Y Z : Complex ℤ} (f : Y ⟶ Z) (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (z : SSet.π₀ ((carrierFramedLimitConeSpace ℤ ℕ Z).obj F)) :
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    carrierFramedLimitConePiZeroEquiv ℤ ℕ Y F
        (SSet.mapπ₀ ((carrierFramedLimitConeSourceMap ℤ ℕ f).app F) z) =
      QD.map ((Functor.const ℕ).map f) ≫ carrierFramedLimitConePiZeroEquiv ℤ ℕ Z F z := by
  exact carrierFramedLimitConePiZeroEquiv_source ℤ ℕ f F z

-- 局所化 Hom の任意の射に対し、元の始域・終域の射の両方に同時に自然。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example {Y Z : Complex ℤ} (f : Y ⟶ Z)
    {F G : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra} (g : F ⟶ G) :
    let := projectiveModelCategory ℤ
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (Complex ℤ)).Q
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    ∀ x : QD.obj ((Functor.const ℕ).obj Z) ⟶ QD.obj ((Diagram.forget ℤ ℕ).obj F),
      carrierFramedLimitDerivedHomEquiv ℤ ℕ Y G
        (QD.map ((Functor.const ℕ).map f) ≫ x ≫ QD.map ((Diagram.forget ℤ ℕ).map g)) =
      Q.map f ≫ carrierFramedLimitDerivedHomEquiv ℤ ℕ Z F x ≫
        Q.map ((framedLimitFunctor ℤ ℕ).map g).hom := by
  exact carrierFramedLimitDerivedHomEquiv_both ℤ ℕ f g


-- 任意の複体を頂点とする通常錐は、実際の底の比較射の局所化像へ移る。
open CategoryTheory Limits HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra)
    (c : Cone ((Diagram.forget ℤ ℕ).obj F)) :
    let := projectiveModelCategory ℤ
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (Complex ℤ)).Q
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    carrierFramedLimitDerivedHomEquiv ℤ ℕ c.pt F (QD.map c.π) =
      Q.map (carrierConeToFramedLimit ℤ ℕ F c) := by
  exact carrierFramedLimitDerivedHomEquiv_cone ℤ ℕ F c

-- 元の E 代数錐では既存の代数比較射の底そのものを回収する。
open CategoryTheory Limits HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (F : ℕ ⥤ (BarrattEccles.operad ℤ).Algebra) (c : Cone F) :
    let := projectiveModelCategory ℤ
    let := CarrierDiagram.projectiveModelCategory ℤ ℕ
    let Q := (weakEquivalences (Complex ℤ)).Q
    let QD := (weakEquivalences (ℕ ⥤ Complex ℤ)).Q
    carrierFramedLimitDerivedHomEquiv ℤ ℕ c.pt.carrier F
        (QD.map ((Operad.Algebra.forget (BarrattEccles.operad ℤ)).mapCone c).π) =
      Q.map (coneToFramedLimit ℤ ℕ F c).hom := by
  exact carrierFramedLimitDerivedHomEquiv_forgetCone ℤ ℕ F c


universe e2ComplexLimitUniverse

-- 任意の可換環と小圏で、元の複体極限比較が右導来普遍性を持つ。
open CategoryTheory Limits HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (K : Type e2ComplexLimitUniverse) [SmallCategory K] :
    let := projectiveModelCategory A
    let := BarrattEccles.CarrierDiagram.projectiveModelCategory A K
    (ComplexLimits.localizedFramedLimit A K).IsRightDerivedFunctor
      (ComplexLimits.framedLimitDerivedComparison A K) (weakEquivalences (K ⥤ Complex A)) := by
  exact ComplexLimits.localizedFramedLimit_isRightDerivedFunctor A K

-- 同じ底の比較同型は元の E 代数錐の通常比較射を保持する。
open CategoryTheory Limits HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (K : Type e2ComplexLimitUniverse) [SmallCategory K]
    (F : K ⥤ (BarrattEccles.operad A).Algebra) (c : Cone F) :
    let := projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Q.map (ComplexLimits.coneToFramedLimit A K ((Diagram.forget A K).obj F)
        ((Operad.Algebra.forget (BarrattEccles.operad A)).mapCone c)) ≫
      (carrierFramedLimitComparisonIso A K F).hom = Q.map (coneToFramedLimit A K F c).hom := by
  exact carrierFramedLimitComparisonIso_forgetCone A K F c

-- 底の比較同型はすべての元の図式射に自然。
open CategoryTheory HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (K : Type e2ComplexLimitUniverse) [SmallCategory K]
    {F G : K ⥤ (BarrattEccles.operad A).Algebra} (g : F ⟶ G) :
    let := projectiveModelCategory A
    let Q := (weakEquivalences (Complex A)).Q
    Q.map ((ComplexLimits.framedLimitFunctor A K).map ((Diagram.forget A K).map g)) ≫
        (carrierFramedLimitComparisonIso A K G).hom =
      (carrierFramedLimitComparisonIso A K F).hom ≫
        Q.map ((framedLimitFunctor A K).map g).hom := by
  exact carrierFramedLimitComparisonIso_naturality A K g

-- 任意の底の右導来極限の値として、元の E 代数計算対象の底を使える。
open CategoryTheory Limits HomotopicalAlgebra SerrePositivity.DifferentialGraded
  SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (K : Type e2ComplexLimitUniverse) [SmallCategory K]
    (F : K ⥤ (BarrattEccles.operad A).Algebra) :
    let := projectiveModelCategory A
    let := CarrierDiagram.projectiveModelCategory A K
    let Q := (weakEquivalences (Complex A)).Q
    let QD := (weakEquivalences (K ⥤ Complex A)).Q
    ∀ (RF : (weakEquivalences (K ⥤ Complex A)).Localization ⥤
        (weakEquivalences (Complex A)).Localization)
      (β : lim ⋙ Q ⟶ QD ⋙ RF),
      RF.IsRightDerivedFunctor β (weakEquivalences (K ⥤ Complex A)) →
      (Q.obj ((framedLimitFunctor A K).obj F).carrier ≅
        RF.obj (QD.obj ((Diagram.forget A K).obj F))) := by
  exact framedLimitCarrierDerivedIso A K F


-- 任意の E 代数に同じ具体的な cofibrant 置換と元への擬同型を供給できる。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X : (BarrattEccles.operad A).Algebra) :
    ∃ Y : CofibrantAlgebra A, ∃ f : (cofibrantAlgebraInclusion A).obj Y ⟶ X, QuasiIso f.hom := by
  let := modelCategory A
  exact ⟨(cofibrantAlgebraReplacement A).obj X,
    (cofibrantAlgebraReplacementComparison A).app X,
    cofibrantAlgebraReplacementComparison_weakEquivalence A X⟩

-- 元の cofibrant 代数射の同じ Map^h の類は、その相対圏での局所化像に一致する。
open CategoryTheory SerrePositivity.EInfinity SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraMappingSpacePiZeroEquiv A X Y
        (mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f)) =
      (cofibrantAlgebraWeakEquivalences A).Q.map f := by
  exact cofibrantAlgebraMappingSpacePiZeroEquiv_class A f

-- 自由解像の全次数の外側の面退化則を、具体的な E 代数相対圏で評価できる。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (n : ℕ) :
    (freeResolutionOuterDegeneracy n).app (cofibrantAlgebraRelativeCategory A) ≫
        (freeResolutionOuterFace n).app (cofibrantAlgebraRelativeCategory A) =
      𝟙 ((freeResolutionLevel n).obj (cofibrantAlgebraRelativeCategory A)) := by
  exact congr_app (freeResolutionOuterDegeneracy_face n) (cofibrantAlgebraRelativeCategory A)

-- 離散可換代数からの同じ cofibrant 模型は、元の離散 E 代数へ擬同型で比較できる。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (B : CommAlgCat A) :
    QuasiIso ((discreteCofibrantAlgebraComparison A).app B).hom := by
  let := modelCategory A
  exact discreteCofibrantAlgebraComparison_weakEquivalence A B


-- 同じ構成的な局所化は全相対関手の合成を厳密に保つ。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization in
example {C D E : RelativeCategory} (F : C ⟶ D) (G : D ⟶ E) :
    strictLocalizationMap (F ≫ G) = strictLocalizationMap F ⋙ strictLocalizationMap G := by
  exact strictLocalizationMap_comp F G

-- 全単体作用素の恒等式は具体的な cofibrant E 代数の次数ごとの局所化でも厳密。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    {n m k : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (φ : m ⟶ k) :
    ((cofibrantAlgebraLocalizedFreeResolution A).map (θ ≫ φ)).toFunctor =
      ((cofibrantAlgebraLocalizedFreeResolution A).map θ).toFunctor ⋙
        ((cofibrantAlgebraLocalizedFreeResolution A).map φ).toFunctor := by
  exact congrArg Cat.Hom.toFunctor ((cofibrantAlgebraLocalizedFreeResolution A).map_comp θ φ)


-- 対象の表示は全単体作用素で保たれ、cofibrant E 代数へそのまま代入できる。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (X : (cofibrantAlgebraRelativeCategory A).category) :
    ((cofibrantAlgebraLocalizedFreeResolution A).map θ).toFunctor.obj
        (localizedFreeResolutionObject (cofibrantAlgebraRelativeCategory A) n X) =
      localizedFreeResolutionObject (cofibrantAlgebraRelativeCategory A) m X := by
  exact localizedFreeResolutionObject_naturality (cofibrantAlgebraRelativeCategory A) θ X


-- 固定 Hom の全単体作用素は元の厳密な合成則を保つ。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization in
example (C : RelativeCategory) (X Y : C.category) {n m k : SimplexCategoryᵒᵖ}
    (θ : n ⟶ m) (φ : m ⟶ k) (f : (localizationHom C X Y).obj n) :
    (localizationHom C X Y).map (θ ≫ φ) f =
      (localizationHom C X Y).map φ ((localizationHom C X Y).map θ f) := by
  exact ConcreteCategory.congr_hom ((localizationHom C X Y).map_comp θ φ) f

-- Kan 化への同じ単位は元の豊穣合成を厳密に保つ。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity.SimplicialLocalization in
example (C : RelativeCategory) (X Y Z : C.category) :
    localizationComposition C X Y Z ≫
        SerrePositivity.KST.Comparison.exInfinityUnit.app (localizationHom C X Z) =
      (SerrePositivity.KST.Comparison.exInfinityUnit.app (localizationHom C X Y) ⊗ₘ
        SerrePositivity.KST.Comparison.exInfinityUnit.app (localizationHom C Y Z)) ≫
          Functor.LaxMonoidal.μ SerrePositivity.KST.Comparison.exInfinity _ _ ≫
            SerrePositivity.KST.Comparison.exInfinity.map (localizationComposition C X Y Z) := by
  exact (kanLocalizationUnit C).map_comp X Y Z

-- 任意の可換環で CAlg_R の quasicategory 性に追加のモデル入力は不要。
open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] : SSet.Quasicategory (CAlg_R A) := by
  infer_instance

-- 任意の可換環で、実際の CAlg_R の全 Hom は同じ Ex∞ から Kan となる。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : CAlgSimplicialCategory A) :
    SSet.KanComplex (SimplicialCategory.sHom X Y) := by
  exact cAlg_sHom_kanComplex A X Y

-- 元の代数の頂点から回収する対象は、指定済みの同じ cofibrant 置換。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X : (BarrattEccles.operad A).Algebra) :
    (cAlgVertexEquiv A).symm (cAlgVertex A X) = (cofibrantAlgebraDKReplacement A).obj X := by
  exact (cAlgVertexEquiv A).symm_apply_apply _

-- 全解像の係数射は具体的な E 代数相対関手に対しても元の augmentation を保つ。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (n : SimplexCategoryᵒᵖ) :
    (localizedFreeResolutionMap (cAlgForgetRelative A)).app n ≫
        (localizedFreeResolutionAugmentation (complexRelativeCategory A)).app n =
      (localizedFreeResolutionAugmentation (cofibrantAlgebraRelativeCategory A)).app n ≫
        strictLocalizationFunctor.map (cAlgForgetRelative A) := by
  exact localizedFreeResolutionMap_augmentation (cAlgForgetRelative A) n

-- 全複体の局所化への忘却射に底の cofibrancy やモデル構造の入力仮定は不要。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X : (SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (cAlgForgetLocalization A).app (Opposite.op (SimplexCategory.mk 0)) (cAlgVertex A X) =
      localizationNerveVertexEquiv (complexRelativeCategory A)
        ((cofibrantAlgebraDKForget A).obj ((cofibrantAlgebraDKReplacement A).obj X)) := by
  exact cAlgForgetLocalization_vertex A X

open SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] :
    SSet.Quasicategory (complexLocalizationNerve A) := by
  infer_instance

-- 局所化 nerve の係数作用は厳密に恒等と合成を保つ。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization in
example {C D E : RelativeCategory} (F : C ⟶ D) (G : D ⟶ E) :
    localizationNerveMap (F ≫ G) = localizationNerveMap F ≫ localizationNerveMap G := by
  exact localizationNerveMap_comp F G

open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization in
example (C : RelativeCategory) : localizationNerveMap (𝟙 C) = 𝟙 (localizationNerve C) := by
  exact localizationNerveMap_id C

-- 元の具体的な E 代数射の DK 成分を戻すと、同じ相対圏の Q の射になる。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    (localizationComponentsAugmentation (cofibrantAlgebraRelativeCategory A)).map
        (localizationArrowClass (cofibrantAlgebraRelativeCategory A) f) =
      (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q.map f := by
  exact localizationComponentsAugmentation_arrow (cofibrantAlgebraRelativeCategory A) f

-- DK Hom の π₀ の圏は、任意の相対圏の元の指定矢の普通の局所化となる。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization in
example (C : RelativeCategory) : (localizationComponentsQ C).IsLocalization C.weakEquivalences := by
  exact localizationComponentsQ_isLocalization C

-- CAlg_R の実際の Kan Hom と元の Map^h の π₀ 比較は、同じ元の代数射の類を回収する。
open CategoryTheory SerrePositivity.EInfinity.SimplicialLocalization
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {X Y : CofibrantAlgebra A} (f : X ⟶ Y) :
    cofibrantAlgebraKanDKPiZeroEquiv A X Y
        (SSet.mapπ₀ (SerrePositivity.KST.Comparison.exInfinityUnit.app
          (localizationHom (cofibrantAlgebraRelativeCategory A)
            (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)))
          (localizationArrowClass (cofibrantAlgebraRelativeCategory A)
            ((ULiftHom.up.{e2ComplexLimitUniverse, e2ComplexLimitUniverse + 1,
              e2ComplexLimitUniverse + 1} (C := CofibrantAlgebra A)).map f))) =
      mappingSpaceClass A ((cofibrantAlgebraInclusion A).map f) := by
  exact cofibrantAlgebraKanDKPiZeroEquiv_class A f

-- 同じ Map^h の全作用素を含む特殊な三本矢への図式で左の全縦射が擬同型となる。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {X Y : (BarrattEccles.operad A).Algebra}
    {s t : ((((mappingSpace A).obj (Opposite.op X)).obj Y).Elements)ᵒᵖ} (f : s ⟶ t) :
    QuasiIso (((mappingSpaceSpecialHammockFunctor A X Y).map f).left).hom := by
  exact mappingSpaceSpecialHammockFunctor_left_quasiIso A f

-- 全単体の比較は、任意の可換環上の元の分解と同じ nerve の射として公開される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    nerve (ULiftHom.{e2ComplexLimitUniverse + 1}
      (((((mappingSpace A).obj (Opposite.op X)).obj Y).Elements)ᵒᵖ)) ⟶
        nerve (algebraSpecialHammock A X Y) :=
  mappingSpaceSpecialHammockNerveMap A X Y

-- 共通比較の左射の反転性は任意の可換環で単体集合モデルの仮定なしに使える。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceIndexAugmentation A X Y)) :=
  mappingSpaceIndexAugmentation_localized_isIso A X Y

-- 任意の次数の単体を表す頂点で、左射と三本矢への右射は同じ局所化射を与える。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity
  SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra)
    (s : ((((mappingSpace A).obj (Opposite.op X)).obj Y).Elements)ᵒᵖ) :
    let := modelCategory A
    FrameHom.SpecialHammock.value ((mappingSpaceSpecialHammockFunctor A X Y).obj s) =
      mappingSpacePiZeroEquiv A (weakEquivalences (BarrattEccles.operad A).Algebra).Q
        (Opposite.op X) Y (SSet.π₀.mk
          (((mappingSpaceIndexAugmentation A X Y).app (Opposite.op (SimplexCategory.mk 0))
            (ComposableArrows.mk₀ (show ULiftHom.{e2ComplexLimitUniverse + 1}
              (((((mappingSpace A).obj (Opposite.op X)).obj Y).Elements)ᵒᵖ) from s))).down)) :=
  mappingSpaceSpanComparison_vertex A X Y s

-- 元の写像空間に使う分解は、任意の自明 fibration を終点とする全 comma 圏で可縮。
-- 単体集合モデルや元の E 代数の cofibrancy の仮定は加えない。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X : (BarrattEccles.operad A).Algebra) (t : algebraTrivialFibrationOver A X) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (SSet.stdSimplex.isTerminalObj₀.from
        (nerve (CostructuredArrow (mappingResolutionOverFunctor A X) t)))) :=
  mappingResolutionCommaTerminal_localized_isIso A X t

-- 同じ写像空間に使う分解の nerve の余終性には単体集合モデルの入力が不要。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles
  SerrePositivity.InfinityCategories in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X : (BarrattEccles.operad A).Algebra) :
    IsLeftCofinal (nerveMap (mappingSmallResolutionOverFunctor A X)) :=
  mappingSmallResolutionOverFunctor_isLeftCofinal A X

-- 分解の元の比較射の弱同値は、元の両端の Kan 性を要求しない。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles
  SerrePositivity.InfinityCategories in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X : (BarrattEccles.operad A).Algebra) :
    IsWeakHomotopyEquivalence (nerveMap (mappingSmallResolutionOverFunctor A X)) :=
  mappingSmallResolutionOverFunctor_isWeakHomotopyEquivalence A X

-- 右脚の全図式の nerve を経由しても、元の右比較射を全単体で厳密に回収する。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    mappingSpaceSpanGrothendieckNerveMap A X Y ≫ algebraSpanFromGrothendieckNerveMap A X Y =
      mappingSpaceSpecialHammockNerveMap A X Y :=
  mappingSpaceSpanGrothendieckNerveMap_fac A X Y

-- 任意の可換環で全右脚の全遷移の Hom は反転され、元の代数に追加仮定を要求しない。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    {X Y : (BarrattEccles.operad A).Algebra} {s t : algebraRightSpanBase A Y} (f : s ⟶ t) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      ((mappingRightHomDiagram A X Y).map f)) :=
  mappingRightHomDiagram_map_localized_isIso A f

-- 全図式の回収は同型へ送られ、元の右比較の反転性は同じ中間射へ帰着される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (algebraSpanFromGrothendieckNerveMap A X Y)) :=
  algebraSpanFromGrothendieckNerveMap_localized_isIso A X Y

-- 同じ分解の比較は全固定右対象で余終であり、元の代数に cofibrancy を要求しない。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles
  SerrePositivity.InfinityCategories in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X V : (BarrattEccles.operad A).Algebra) :
    IsLeftCofinal (nerveMap (mappingResolutionFixedRightComparison A X V)) :=
  mappingResolutionFixedRightComparison_isLeftCofinal A X V

-- 同じ成分の可逆性は弱同値という別のクラスを仮定せず、元の anodyne 局所化で読む。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X V : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap (mappingResolutionFixedRightComparison A X V))) :=
  mappingResolutionFixedRightComparison_localized_isIso A X V

-- 全右脚に自然な元の図式の全成分で、同じ比較射が反転される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra)
    (t : AsSmall.{e2ComplexLimitUniverse + 1} (algebraRightSpanBase A Y)) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap ((mappingFixedRightDiagramComparison A X Y).app t).toFunctor)) :=
  mappingFixedRightDiagramComparison_localized_isIso A X Y t

-- 元の全右脚の図式の比較そのものは、各 comma の収縮から反転される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap (mappingFixedRightGrothendieckComparison A X Y))) :=
  mappingFixedRightGrothendieckComparison_localized_isIso A X Y

-- 全図式の元の比較は comma の左変数の比較と全対象・全射で厳密に可換。
open CategoryTheory SerrePositivity.EInfinity.FrameHom in
example {K L C J : Type e2ComplexLimitUniverse} [Category.{e2ComplexLimitUniverse} K]
    [Category.{e2ComplexLimitUniverse} L] [Category.{e2ComplexLimitUniverse} C]
    [Category.{e2ComplexLimitUniverse} J] (P : K ⥤ L) (Q : L ⥤ C) (R : J ⥤ C) :
    fixedRightGrothendieckComparison P Q R ⋙ CommaGrothendieck.toComma Q R =
      CommaGrothendieck.toComma (P ⋙ Q) R ⋙ Comma.preLeft P Q R :=
  fixedRightGrothendieckComparison_toComma P Q R

-- 元の全右脚の bar 比較は、任意の可換環で同じ自然変換そのものに適用される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      ((SerrePositivity.SimplicialModel.BarConstruction.functor
        (algebraRightSpanBase A Y)).map (mappingRightHomFromIdentity A X Y))) :=
  mappingRightHomFromIdentity_bar_localized_isIso A X Y

-- 図式の比較の成分は、元の指定右脚による実際の後合成に厳密に一致する。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (t : algebraRightSpanBase A Y) :
    let := modelCategory A
    (mappingRightHomFromIdentity A X Y).app t =
      (SerrePositivity.HomotopyFunctionComplex.cosimplicialHom
        ((SerrePositivity.Reedy.cosimplicialResolutionFamily
          (mappingCofibrantFactorization A)).obj.obj X)).map t.hom :=
  mappingRightHomFromIdentity_app A X Y t

-- 元の定値 bar の射は、値と添字の独立した宇宙で最初のラベルを返し、反転される。
open CategoryTheory CategoryTheory.Limits SerrePositivity.EInfinity.FrameHom in
example {D : Type e2ComplexLimitUniverse} [Category.{0} D] (K : SSet.{0})
    {i : D} (hi : IsInitial i) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (ConstantBar.augmentation D K)) :=
  ConstantBar.augmentation_localized_isIso D K hi

-- 元の Map^h と同じ fibrant 置換の右脚を使う包含そのものは、任意の可換環で反転。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceBarInclusion A X Y)) :=
  mappingSpaceBarInclusion_localized_isIso A X Y

-- 元の全単体の共通始域から同じ bar への合成射も反転される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceIndexBarMap A X Y)) :=
  mappingSpaceIndexBarMap_localized_isIso A X Y

-- 全単体で、同じ元の Map^h の単体と元の fibrant 置換の右脚を保持。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles Opposite in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (n : SimplexCategoryᵒᵖ)
    (x : (((mappingSpace A).obj (op X)).obj Y).obj n) :
    (mappingSpaceBarInclusion A X Y).app n (ULift.up x) =
      (Functor.const _).obj (((mappingRightHomDiagram A X Y).flip.obj n).elementsMk
        (mappingFibrantRightLeg A Y) x) :=
  mappingSpaceBarInclusion_app A X Y n x

-- 元の Cat 値の右脚図式にも、同じ fiber 包含を回収する厳密な比較を適用できる。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles
  SerrePositivity.EInfinity.FrameHom in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (t : algebraRightSpanBase A Y) :
    BarRows.valueInclusion (Thomason.nerveDiagram (algebraSpanRightDiagram A X Y)) t ≫
        Thomason.map (algebraSpanRightDiagram A X Y) =
      Thomason.fiberNerveMap (algebraSpanRightDiagram A X Y) t :=
  Thomason.valueInclusion_map (algebraSpanRightDiagram A X Y) t

-- 任意の関手の comma 図式の射影は、独立した値と添字の宇宙で反転される。
open CategoryTheory SerrePositivity.EInfinity.FrameHom in
example {E : Type} [Category.{0} E] {D : Type e2ComplexLimitUniverse} [Category.{0} D]
    (p : E ⥤ D) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (CommaNerve.barProjection p)) :=
  CommaNerve.barProjection_localized_isIso p

-- 同じ全右脚の比較は bar でも反転される。Thomason 射の反転性は仮定しない。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingResolutionBarComparison A X Y)) :=
  mappingResolutionBarComparison_localized_isIso A X Y

-- 元の全図式の比較そのものと bar の比較は、同じ二つの Thomason 射で厳密に可換。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles
  SerrePositivity.EInfinity.FrameHom in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    Thomason.map (mappingSmallResolutionRightDiagram A X Y) ≫
        nerveMap (mappingFixedRightGrothendieckComparison A X Y) =
      mappingResolutionBarComparison A X Y ≫
        Thomason.map (mappingSmallSpanRightDiagram A X Y) :=
  mappingResolutionThomasonSquare A X Y

-- 任意の小さい Cat 値図式の元の Thomason 射に反転性を適用できる。
-- 単体集合モデルや fiber の Kan 性の入力は不要。
open CategoryTheory SerrePositivity.EInfinity.FrameHom in
example {D : Type e2ComplexLimitUniverse} [Category.{e2ComplexLimitUniverse} D]
    (G : D ⥤ Cat.{e2ComplexLimitUniverse, e2ComplexLimitUniverse}) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map (Thomason.map G)) :=
  Thomason.map_localized_isIso G

-- 同じ元の射は F1b の弱ホモトピー同値にもなる。
open CategoryTheory SerrePositivity.EInfinity.FrameHom in
example {D : Type e2ComplexLimitUniverse} [Category.{e2ComplexLimitUniverse} D]
    (G : D ⥤ Cat.{e2ComplexLimitUniverse, e2ComplexLimitUniverse}) :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence (Thomason.map G) :=
  Thomason.map_isWeakHomotopyEquivalence G

-- 任意の可換環で、全右脚上の元の分解の Thomason 射が反転される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles
  SerrePositivity.EInfinity.FrameHom in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (Thomason.map (mappingSmallResolutionRightDiagram A X Y))) :=
  mappingResolutionThomason_localized_isIso A X Y

-- 同じ全右脚上の全左脚側の Thomason 射も、元の代数の cofibrancy なしで反転。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles
  SerrePositivity.EInfinity.FrameHom in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (Thomason.map (mappingSmallSpanRightDiagram A X Y))) :=
  mappingSpanThomason_localized_isIso A X Y

-- 元の固定 fiber の nerve の包含は、始対象と全遷移の不変性だけから反転される。
open CategoryTheory CategoryTheory.Limits SerrePositivity.EInfinity.FrameHom in
example {D : Type e2ComplexLimitUniverse} [Category.{e2ComplexLimitUniverse} D]
    (G : D ⥤ Cat.{e2ComplexLimitUniverse, e2ComplexLimitUniverse})
    {i : D} (hi : IsInitial i)
    (hG : ∀ {d e : D} (f : d ⟶ e),
      IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (nerveMap (G.map f).toFunctor))) (d : D) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (Thomason.fiberNerveMap G d)) :=
  Thomason.fiberNerveMap_localized_isIso G hi hG d

-- 任意の可換環で、元の全右脚の各遷移そのものを反転できる。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    {X Y : (BarrattEccles.operad A).Algebra}
    {s t : AsSmall.{e2ComplexLimitUniverse + 1} (algebraRightSpanBase A Y)} (f : s ⟶ t) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (nerveMap ((mappingSmallResolutionRightDiagram A X Y).map f).toFunctor)) :=
  mappingSmallResolutionRightDiagram_map_localized_isIso A f

-- 同じ元の共通始域から全左脚・全右脚の小さい全図式への射も反転される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceSmallSpanGrothendieckNerveMap A X Y)) :=
  mappingSpaceSmallSpanGrothendieckNerveMap_localized_isIso A X Y

-- 全次数で、元の中間射そのものを保持する。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles Opposite in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (n : SimplexCategoryᵒᵖ)
    (c : (nerve (ULiftHom.{e2ComplexLimitUniverse + 1}
      (((((mappingSpace A).obj (op X)).obj Y).Elements)ᵒᵖ))).obj n)
    (j : Fin (n.unop.len + 1)) :
    (((mappingSpaceSmallSpanGrothendieckNerveMap A X Y).app n c).obj j).fiber.hom.down =
      (c.obj j).unop.val :=
  mappingSpaceSmallSpanGrothendieckNerveMap_hom A X Y n c j

-- 元の小さい全図式からの回収は、全単体・全作用素で元の右射そのものを返す。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    mappingSpaceSmallSpanGrothendieckNerveMap A X Y ≫ mappingSmallSpanRecoveryNerveMap A X Y =
      mappingSpaceSpecialHammockNerveMap A X Y :=
  mappingSpaceSmallSpanGrothendieckNerveMap_fac A X Y

-- 任意の可換環上で同じ元の右比較射が反転される。単体集合モデルの仮定は不要。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceSpecialHammockNerveMap A X Y)) :=
  mappingSpaceSpecialHammockNerveMap_localized_isIso A X Y

-- 同じ元の三本矢の nerve が Kan であるという入力なしに、右射は弱ホモトピー同値。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
      (mappingSpaceSpecialHammockNerveMap A X Y) :=
  mappingSpaceSpecialHammockNerveMap_isWeakHomotopyEquivalence A X Y

-- 同じ二射から定めた同型を元の左射へ合成すると、元の右射に厳密に一致する。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceSpecialHammockComparisonIso A X Y).hom =
      SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceSpecialHammockNerveMap A X Y) :=
  mappingSpaceSpecialHammockComparisonIso_fac A X Y

-- 実際の二つの関手的分解を使い、任意の元の代数で三本矢の包含を反転する。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (algebraSpecialThreeArrowInclusionNerveMap A X Y)) :=
  algebraSpecialThreeArrowInclusionNerveMap_localized_isIso A X Y

-- 同じ元の Map^h の共通始域から一般の三本矢へ入れる射そのものも反転される。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceWeakThreeArrowNerveMap A X Y)) :=
  mappingSpaceWeakThreeArrowNerveMap_localized_isIso A X Y

-- 元の比較の弱同値性は三本矢の nerve の Kan 性を入力しない。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
      (mappingSpaceWeakThreeArrowNerveMap A X Y) :=
  mappingSpaceWeakThreeArrowNerveMap_isWeakHomotopyEquivalence A X Y

-- 元の左射の後の同型は、元の一般の三本矢への右比較を回収する。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceWeakThreeArrowComparisonIso A X Y).hom =
      SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceWeakThreeArrowNerveMap A X Y) :=
  mappingSpaceWeakThreeArrowComparisonIso_fac A X Y

-- 語の射の合成は元の色を保つ単調写像の合成。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b c : Word} (f : a ⟶ b) (g : b ⟶ c) (i : Fin a.length) :
    (f ≫ g).orderHom i = g.orderHom (f.orderHom i) := Word.comp_apply f g i

-- 元の三本矢の包含そのものが三列の zigzag 圏の同値を与える。
open CategoryTheory HomotopicalAlgebra SerrePositivity.EInfinity in
example {C : Type e2ComplexLimitUniverse} [Category C] [ModelCategory C] (X Y : C) :
    (Hammock.ThreeArrow.functor (X := X) (Y := Y)).IsEquivalence := inferInstance

-- 任意の可換環上で、同じ元の共通始域から実際の三列の graph へ入れる射も反転。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
      (mappingSpaceHammockGraphNerveMap A X Y)) :=
  mappingSpaceHammockGraphNerveMap_localized_isIso A X Y

-- 三列の graph の Kan 性を追加仮定せず、元の比較は弱ホモトピー同値。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
      (mappingSpaceHammockGraphNerveMap A X Y) :=
  mappingSpaceHammockGraphNerveMap_isWeakHomotopyEquivalence A X Y

-- 元の左射との合成は、同じ三列の graph への右射を厳密に回収。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceIndexAugmentation A X Y) ≫
        (mappingSpaceHammockGraphComparisonIso A X Y).hom =
      SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceHammockGraphNerveMap A X Y) :=
  mappingSpaceHammockGraphComparisonIso_fac A X Y

-- 語の合成の切断位置は、同じ元の切断の逆順の合成。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b c : Word} (f : a ⟶ b) (g : b ⟶ c) (j : Fin (c.length + 1)) :
    (f ≫ g).cut j = f.cut (g.cut j) := Word.Hom.cut_comp f g j

-- 空 fiber の合成は、元の圏の同じ恒等射。乗法性すら追加入力にしない。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    {w : Word} {X Y : C} (S : Zigzag W w X Y) (d : Direction)
    (p : Fin (w.length + 1))
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < p.val → w.direction i = d) :
    Segment.map d S p p le_rfl hd = 𝟙 (Direction.vertex d (S.vertex p)) :=
  Segment.map_refl d S p hd

-- 任意の可換環で、語の写像から元の graph 間の実際の射を構成できる。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word} (f : a ⟶ b)
    (X Y : (BarrattEccles.operad A).Algebra) :
    Nonempty (BarrattEccles.algebraHammockGraph A a X Y ⟶
      BarrattEccles.algebraHammockGraph A b X Y) :=
  ⟨BarrattEccles.algebraHammockGraphMap A f X Y⟩

-- モデル instance を入力せず、全縦射で元の同じ切断位置の射を回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word} (f : a ⟶ b)
    (X Y : (BarrattEccles.operad A).Algebra)
    {S T : BarrattEccles.algebraHammockZigzag A a X Y} (g : S ⟶ T)
    (j : Fin (b.length + 1)) :
    ((BarrattEccles.algebraHammockTransition A f X Y).map g).app j = g.app (f.cut j) :=
  BarrattEccles.algebraHammockTransition_app A f X Y g j

-- 恒等語の元の遷移は、全対象・全縦射の恒等関手。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] (w : Word) (X Y : C) :
    WordAction.functor (W := W) (X := X) (Y := Y) (𝟙 w) = 𝟭 (Zigzag W w X Y) :=
  WordAction.functor_id

-- 語の合成は、同じ元の遷移関手の厳密な合成。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] {a b c : Word} (f : a ⟶ b) (g : b ⟶ c) (X Y : C) :
    WordAction.functor (W := W) (X := X) (Y := Y) (f ≫ g) =
      WordAction.functor f ⋙ WordAction.functor g :=
  WordAction.functor_comp f g

-- 元の同方向区間の分割則には、射の類の乗法性を要求しない。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    {w : Word} {X Y : C} (S : Zigzag W w X Y) (d : Direction)
    (p q r : Fin (w.length + 1)) (hpq : p ≤ q) (hqr : q ≤ r)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < r.val → w.direction i = d) :
    Segment.map d S p r (hpq.trans hqr) hd =
      Segment.map d S p q hpq (fun i hi hi' => hd i hi (by omega)) ≫
        Segment.map d S q r hqr (fun i hi hi' => hd i (by omega) hi') :=
  Segment.map_comp d S p q r hpq hqr hd

-- 任意の可換環上の同じ元の全語の余錐は、実際に単体集合の余極限。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra) :
    Limits.IsColimit (algebraHammockGraphCocone A X Y) :=
  algebraHammockGraphCocone_isColimit A X Y

-- 列の圧縮と空列挿入の元の射は、同じ余極限の標準射と可換。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    {a b : Hammock.Word} (f : a ⟶ b) :
    BarrattEccles.algebraHammockGraphMap A f X Y ≫
        BarrattEccles.algebraHammockGraphInclusion A b X Y =
      BarrattEccles.algebraHammockGraphInclusion A a X Y :=
  BarrattEccles.algebraHammockGraphInclusion_naturality A X Y f

-- 同じ元の Map^h の左射の後の比較は、全語の余極限への元の右射を回収。
open CategoryTheory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra) :
    SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceIndexAugmentation A X Y) ≫ mappingSpaceHammockColimitComparison A X Y =
      SerrePositivity.SimplicialModel.AnodyneHomotopy.anodyneQ.map
        (mappingSpaceHammockColimitNerveMap A X Y) :=
  mappingSpaceHammockColimitComparison_fac A X Y

-- 語の連結関手の射は、元の二つの語の写像の合成を厳密に保持する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b a' b' a'' b'' : Word} (f : a ⟶ a') (g : b ⟶ b')
    (f' : a' ⟶ a'') (g' : b' ⟶ b'') :
    Word.appendMap (f ≫ f') (g ≫ g') = Word.appendMap f g ≫ Word.appendMap f' g' :=
  Word.appendMap_comp f g f' g'

-- 連結した写像の左側の全切断は元の左の切断。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b a' b' : Word} (f : a ⟶ a') (g : b ⟶ b') (j : Fin (a'.length + 1)) :
    (Word.appendMap f g).cut (Word.leftVertex a' b' j) = Word.leftVertex a b (f.cut j) :=
  Word.cut_append_left f g j

-- 右側も接合点を含めて元の同じ切断を回収。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b a' b' : Word} (f : a ⟶ a') (g : b ⟶ b') (j : Fin (b'.length + 1)) :
    (Word.appendMap f g).cut (Word.rightVertex a' b' j) = Word.rightVertex a b (g.cut j) :=
  Word.cut_append_right f g j

-- 接合点の縦射の整合は元の固定端点から従い、モデル構造や乗法性を入力しない。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    {a b : Word} {X Y Z : C} {S S' : Zigzag W a X Y} {T T' : Zigzag W b Y Z}
    (f : Zigzag.Hom S S') (g : Zigzag.Hom T T') :
    HEq (f.app (Fin.last a.length)) (g.app 0) := ZigzagAppend.joint_app_heq f g

-- 任意の可換環上の同じ graph の合成は、全単体の全縦射を厳密に保持する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (a b : Hammock.Word)
    (X Y Z : (BarrattEccles.operad A).Algebra) (n : SimplexCategoryᵒᵖ)
    (σ : (BarrattEccles.algebraHammockGraph A a X Y).obj n)
    (τ : (BarrattEccles.algebraHammockGraph A b Y Z).obj n)
    {i j : Fin (n.unop.len + 1)} (h : i ⟶ j) :
    ((BarrattEccles.algebraHammockGraphComposition A a b X Y Z).app n (σ, τ)).map h =
      Hammock.ZigzagAppend.map (σ.map h) (τ.map h) :=
  BarrattEccles.algebraHammockGraphComposition_map A a b X Y Z n σ τ h

-- 同じ元の空語から全語の余極限への単位射を、モデル instance の入力なしで構成。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity.BarrattEccles in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X : (BarrattEccles.operad A).Algebra) :
    Nonempty (𝟙_ SSet.{e2ComplexLimitUniverse + 1} ⟶ algebraHammockColimitGraph A X X) :=
  ⟨algebraHammockColimitUnit A X⟩

-- 左の部分区間の回収には、射の類の乗法性やモデル構造を入力しない。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    {a b : Word} {X Y Z : C} (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (d : Direction)
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    HEq (Segment.map d (ZigzagAppend.obj S T) (Word.leftVertex a b p) (Word.leftVertex a b q)
      (Word.leftVertex_mono a b hpq) (Word.append_left_direction a b d p q hd))
      (Segment.map d S p q hpq hd) := ZigzagAppend.map_left_heq S T d p q hpq hd

-- 右の部分区間も、元の接合点と空区間を含めて同じ合成を回収。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    {a b : Word} {X Y Z : C} (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (d : Direction)
    (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin b.length, p.val ≤ i.val → i.val < q.val → b.direction i = d) :
    HEq (Segment.map d (ZigzagAppend.obj S T) (Word.rightVertex a b p) (Word.rightVertex a b q)
      (Word.rightVertex_mono a b hpq) (Word.append_right_direction a b d p q hd))
      (Segment.map d T p q hpq hd) := ZigzagAppend.map_right_heq S T d p q hpq hd

-- 元の連結関手と全語の遷移は、同型だけでなく関手として厳密に一致する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] {a b a' b' : Word} (f : a ⟶ a') (g : b ⟶ b') (X Y Z : C) :
    ZigzagAppend.functor (W := W) (a := a) (b := b) (X := X) (Y := Y) (Z := Z) ⋙
        WordAction.functor (Word.appendMap f g) =
      (WordAction.functor (W := W) (X := X) (Y := Y) f).prod
        (WordAction.functor (W := W) (X := Y) (Y := Z) g) ⋙ ZigzagAppend.functor :=
  ZigzagAppend.functor_naturality f g

-- 任意の可換環上の同じ graph の合成は、元の両語の全遷移に自然。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b a' b' : Hammock.Word}
    (f : a ⟶ a') (g : b ⟶ b') (X Y Z : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockGraphMap A f X Y ⊗ₘ BarrattEccles.algebraHammockGraphMap A g Y Z) ≫
        BarrattEccles.algebraHammockGraphComposition A a' b' X Y Z =
      BarrattEccles.algebraHammockGraphComposition A a b X Y Z ≫
        BarrattEccles.algebraHammockGraphMap A (Hammock.Word.appendMap f g) X Z :=
  BarrattEccles.algebraHammockGraphComposition_naturality A f g X Y Z

-- 対の図式の元の余極限上の比較は、全固定語の元の合成を厳密に回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (a b : Hammock.Word)
    (X Y Z : (BarrattEccles.operad A).Algebra) :
    Limits.colimit.ι (BarrattEccles.algebraHammockPairDiagram A X Y Z) (a, b) ≫
        BarrattEccles.algebraHammockColimitCompositionPairing A X Y Z =
      BarrattEccles.algebraHammockGraphComposition A a b X Y Z ≫
        BarrattEccles.algebraHammockGraphInclusion A (Hammock.Word.append a b) X Z :=
  BarrattEccles.algebraHammockColimitCompositionPairing_fac A a b X Y Z

-- 単体集合のモデル構造なしで、二つの元の余極限の積から合成を回収する。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (a b : Hammock.Word)
    (X Y Z : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockGraphInclusion A a X Y ⊗ₘ
        BarrattEccles.algebraHammockGraphInclusion A b Y Z) ≫
        BarrattEccles.algebraHammockColimitComposition A X Y Z =
      BarrattEccles.algebraHammockGraphComposition A a b X Y Z ≫
        BarrattEccles.algebraHammockGraphInclusion A (Hammock.Word.append a b) X Z :=
  BarrattEccles.algebraHammockColimitComposition_fac A a b X Y Z

-- 対の図式の余極限との標準同型は、元の全標準射を保持する。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (a b : Hammock.Word)
    (X Y Z : (BarrattEccles.operad A).Algebra) :
    Limits.colimit.ι (BarrattEccles.algebraHammockPairDiagram A X Y Z) (a, b) ≫
        (BarrattEccles.algebraHammockTensorPairColimitIso A X Y Z).hom =
      (BarrattEccles.algebraHammockGraphInclusion A a X Y ⊗ₘ
        BarrattEccles.algebraHammockGraphInclusion A b Y Z) :=
  BarrattEccles.algebraHammockTensorPairColimitIso_fac A a b X Y Z

-- 同じ標準同型と実際の積からの合成は、前工程の比較そのもの。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y Z : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockTensorPairColimitIso A X Y Z).hom ≫
        BarrattEccles.algebraHammockColimitComposition A X Y Z =
      BarrattEccles.algebraHammockColimitCompositionPairing A X Y Z :=
  BarrattEccles.algebraHammockTensorPairColimitIso_comp A X Y Z

-- 元の全固定語の標準射の積は、実際の積からの射を一意に決める。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y Z : (BarrattEccles.operad A).Algebra) {K : SSet.{e2ComplexLimitUniverse + 1}}
    (f g : BarrattEccles.algebraHammockColimitGraph A X Y ⊗
      BarrattEccles.algebraHammockColimitGraph A Y Z ⟶ K)
    (h : ∀ a b : Hammock.Word,
      (BarrattEccles.algebraHammockGraphInclusion A a X Y ⊗ₘ
        BarrattEccles.algebraHammockGraphInclusion A b Y Z) ≫ f =
      (BarrattEccles.algebraHammockGraphInclusion A a X Y ⊗ₘ
        BarrattEccles.algebraHammockGraphInclusion A b Y Z) ≫ g) : f = g :=
  BarrattEccles.algebraHammockTensorPair_hom_ext A X Y Z f g h

-- 任意の可換環上の元の空語の単位は、実際の余極限上で左単位則を満たす。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockColimitUnit A X ⊗ₘ
        𝟙 (BarrattEccles.algebraHammockColimitGraph A X Y)) ≫
        BarrattEccles.algebraHammockColimitComposition A X X Y =
      (λ_ (BarrattEccles.algebraHammockColimitGraph A X Y)).hom :=
  BarrattEccles.algebraHammockColimitComposition_left_unit A X Y

-- 右単位則も同じ任意の環・元の単位・元の合成に対して成り立つ。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    (𝟙 (BarrattEccles.algebraHammockColimitGraph A X Y) ⊗ₘ
        BarrattEccles.algebraHammockColimitUnit A Y) ≫
        BarrattEccles.algebraHammockColimitComposition A X Y Y =
      (ρ_ (BarrattEccles.algebraHammockColimitGraph A X Y)).hom :=
  BarrattEccles.algebraHammockColimitComposition_right_unit A X Y

-- 全固定語の標準射に制限した左単位則は、同じ元の単位同型を回収する。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (a : Hammock.Word)
    (X Y : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockColimitUnit A X ⊗ₘ
        BarrattEccles.algebraHammockGraphInclusion A a X Y) ≫
        BarrattEccles.algebraHammockColimitComposition A X X Y =
      (λ_ (BarrattEccles.algebraHammockGraph A a X Y)).hom ≫
        BarrattEccles.algebraHammockGraphInclusion A a X Y :=
  BarrattEccles.algebraHammockColimitComposition_left_unit_fac A a X Y

-- 元の連結関手の単位則は、対象だけでなく全縦射を含む厳密な関手の一致。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] (a : Word) (X Y : C) :
    ((Functor.const (Zigzag W a X Y)).obj (emptyObj W X)).prod' (𝟭 _) ⋙
        ZigzagAppend.functor ⋙ WordAction.functor (eqToHom (Word.empty_append a)) =
      𝟭 (Zigzag W a X Y) := ZigzagAppend.empty_left_functor

-- 任意の可換環上で、元の E 代数の全語の余極限は単体的豊穣圏をなす。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] :
    EnrichedCategory SSet.{e2ComplexLimitUniverse + 1} (BarrattEccles.operad A).Algebra :=
  BarrattEccles.algebraHammockEnrichedCategory A

-- 豊穣 Hom と合成は同じ元の余極限・同じ元の合成を厳密に保持する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y Z : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockEnrichedCategory A).comp X Y Z =
      BarrattEccles.algebraHammockColimitComposition A X Y Z :=
  BarrattEccles.algebraHammockEnrichedCategory_comp A X Y Z

-- 結合則は元の三つの実際の余極限の積上で成り立つ。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y Z V : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockColimitComposition A X Y Z ⊗ₘ
        𝟙 (BarrattEccles.algebraHammockColimitGraph A Z V)) ≫
        BarrattEccles.algebraHammockColimitComposition A X Z V =
      (α_ (BarrattEccles.algebraHammockColimitGraph A X Y)
        (BarrattEccles.algebraHammockColimitGraph A Y Z)
        (BarrattEccles.algebraHammockColimitGraph A Z V)).hom ≫
          (𝟙 (BarrattEccles.algebraHammockColimitGraph A X Y) ⊗ₘ
            BarrattEccles.algebraHammockColimitComposition A Y Z V) ≫
              BarrattEccles.algebraHammockColimitComposition A X Y V :=
  BarrattEccles.algebraHammockColimitComposition_assoc A X Y Z V

-- filtered 性を使わず、全固定語の標準射の三重積が射を一意に決める。
open CategoryTheory MonoidalCategory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y Z V : (BarrattEccles.operad A).Algebra) {K : SSet.{e2ComplexLimitUniverse + 1}}
    (f g : (BarrattEccles.algebraHammockColimitGraph A X Y ⊗
      BarrattEccles.algebraHammockColimitGraph A Y Z) ⊗
        BarrattEccles.algebraHammockColimitGraph A Z V ⟶ K)
    (h : ∀ a b c : Hammock.Word,
      ((BarrattEccles.algebraHammockGraphInclusion A a X Y ⊗ₘ
        BarrattEccles.algebraHammockGraphInclusion A b Y Z) ⊗ₘ
          BarrattEccles.algebraHammockGraphInclusion A c Z V) ≫ f =
      ((BarrattEccles.algebraHammockGraphInclusion A a X Y ⊗ₘ
        BarrattEccles.algebraHammockGraphInclusion A b Y Z) ⊗ₘ
          BarrattEccles.algebraHammockGraphInclusion A c Z V) ≫ g) : f = g :=
  BarrattEccles.algebraHammockTensorTriple_hom_ext A X Y Z V f g h

-- 元の三重連結の関手の一致は全対象・全縦射を保持する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] (a b c : Word) (X Y Z V : C) :
    (ZigzagAppend.functor (W := W) (a := a) (b := b) (X := X) (Y := Y) (Z := Z)).prod
        (𝟭 (Zigzag W c Z V)) ⋙ ZigzagAppend.functor ⋙
          WordAction.functor (eqToHom (Word.append_assoc a b c)) =
      CategoryTheory.prod.associator (Zigzag W a X Y) (Zigzag W b Y Z) (Zigzag W c Z V) ⋙
        (𝟭 (Zigzag W a X Y)).prod ZigzagAppend.functor ⋙ ZigzagAppend.functor :=
  ZigzagAppend.functor_assoc

-- 元の包含の各列の両端は、元の同じ切断を厳密に回収する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b : Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom) (i : Fin a.length) :
    f.cut (f.orderHom i).castSucc = i.castSucc ∧ f.cut (f.orderHom i).succ = i.succ :=
  ⟨f.cut_image_castSucc hf i, f.cut_image_succ hf i⟩

-- 任意の可換環上で、元の語の包含による全単体の遷移は単射。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) :
    Mono (BarrattEccles.algebraHammockGraphMap A f X Y) :=
  BarrattEccles.algebraHammockGraphMap_mono A f hf X Y

-- 元の各列は、同じ実際の E 代数の包含の像の位置から回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) (S : BarrattEccles.algebraHammockZigzag A a X Y)
    (i : Fin a.length) :
    HEq (((BarrattEccles.algebraHammockTransition A f X Y).obj S).arrow (f.orderHom i))
      (S.arrow i) := BarrattEccles.algebraHammockTransition_image_arrow_heq A f hf X Y S i

-- 元の遷移関手は縦射を同一視せず、忠実性に追加のモデル入力は不要。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockTransition A f X Y).Faithful :=
  BarrattEccles.algebraHammockTransition_faithful A f hf X Y

-- 像の外の列は、元の同じ切断頂点の恒等射。単射性も不要。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    [W.IsMultiplicative] {a b : Word} {X Y : C} (f : a ⟶ b) (S : Zigzag W a X Y)
    (j : Fin b.length) (hj : ∀ i : Fin a.length, f.orderHom i ≠ j) :
    HEq (Direction.arrow (b.direction j) (WordAction.obj f S) j rfl)
      (𝟙 (Direction.vertex (b.direction j) (S.vertex (f.cut j.castSucc)))) :=
  WordAction.empty_fiber_arrow_heq f S j hj

-- 同じ切断の fiber 上の元の縦射の一致には、語の単射性も不要。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    [W.IsMultiplicative] {a b : Word} {X Y : C} (f : a ⟶ b) {S T : Zigzag W a X Y}
    (g : WordAction.obj f S ⟶ WordAction.obj f T) (p q : Fin (b.length + 1))
    (h : f.cut p = f.cut q) : HEq (g.app p) (g.app q) := WordAction.app_cut_eq f g p q h

-- 任意の可換環上で、同じ元の包含の遷移関手は充満。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockTransition A f X Y).Full :=
  BarrattEccles.algebraHammockTransition_full A f hf X Y

-- 元の包含の像の間の全縦射は、元の縦射として厳密に回収される。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) {S T : BarrattEccles.algebraHammockZigzag A a X Y}
    (g : (BarrattEccles.algebraHammockTransition A f X Y).obj S ⟶
      (BarrattEccles.algebraHammockTransition A f X Y).obj T) :
    (BarrattEccles.algebraHammockTransition A f X Y).map
        (BarrattEccles.algebraHammockTransitionPreimage A f hf X Y g) = g :=
  BarrattEccles.algebraHammockTransition_map_preimage A f hf X Y g

-- 反対の往復も元の同じ縦射に一致し、局所化後だけの一致ではない。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) {S T : BarrattEccles.algebraHammockZigzag A a X Y}
    (g : S ⟶ T) :
    BarrattEccles.algebraHammockTransitionPreimage A f hf X Y
        ((BarrattEccles.algebraHammockTransition A f X Y).map g) = g :=
  BarrattEccles.algebraHammockTransition_preimage_map A f hf X Y g

-- 全次数の元の単体が包含の像に入ることは、元の全行の像で特徴付けられる。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) (n : SimplexCategoryᵒᵖ)
    (τ : (BarrattEccles.algebraHammockGraph A b X Y).obj n) :
    τ ∈ Set.range ((BarrattEccles.algebraHammockGraphMap A f X Y).app n) ↔
      ∀ j, ∃ S : BarrattEccles.algebraHammockZigzag A a X Y,
        (BarrattEccles.algebraHammockTransition A f X Y).obj S = τ.obj j :=
  BarrattEccles.algebraHammockGraphMap_range_iff A f hf X Y n τ

-- 恒等列の条件からの原像は、同じ元の E 代数の zigzag を厳密に回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom) (X Y : (BarrattEccles.operad A).Algebra)
    (R : BarrattEccles.algebraHammockZigzag A b X Y)
    (hR : BarrattEccles.algebraHammockIdentityOutside A f X Y R) :
    (BarrattEccles.algebraHammockTransition A f X Y).obj
        (BarrattEccles.algebraHammockIdentityPreimage A f hf X Y R hR) = R :=
  BarrattEccles.algebraHammockIdentityPreimage_image A f hf X Y R hR

-- 全次数での元の像は、元の全行の恒等列の条件と同値。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b : Hammock.Word}
    (f : a ⟶ b) (hf : Function.Injective f.orderHom) (X Y : (BarrattEccles.operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) (τ : (BarrattEccles.algebraHammockGraph A b X Y).obj n) :
    τ ∈ Set.range ((BarrattEccles.algebraHammockGraphMap A f X Y).app n) ↔
      ∀ j, BarrattEccles.algebraHammockIdentityOutside A f X Y (τ.obj j) :=
  BarrattEccles.algebraHammockGraphMap_range_iff_identityOutside A f hf X Y n τ

-- proper 性は任意の可換環上で実際の同じ全語の図式に成り立つ。
open SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra) :
    Hammock.ProperDiagram (BarrattEccles.algebraHammockGraphDiagram A X Y) :=
  BarrattEccles.algebraHammockGraphDiagram_proper A X Y

-- 列の交わりの像は、同じ元の部分複体の交わりに一致する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b c : Hammock.Word}
    (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) :
    Subfunctor.range ((BarrattEccles.algebraHammockGraphDiagram A X Y).map
      (Hammock.Word.intersectionInclusion f g)) =
        Subfunctor.range ((BarrattEccles.algebraHammockGraphDiagram A X Y).map f) ⊓
          Subfunctor.range ((BarrattEccles.algebraHammockGraphDiagram A X Y).map g) :=
  BarrattEccles.algebraHammockGraphIntersection_range A f g hf hg X Y

-- 原典の交わりへの誘導射そのものが同型で、追加のモデル入力は不要。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b c : Hammock.Word}
    (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) :
    IsIso (BarrattEccles.algebraHammockGraphIntersectionComparison A f g hf hg X Y) :=
  BarrattEccles.algebraHammockGraphIntersectionComparison_isIso A f g hf hg X Y

-- 同じ交わりの比較は、元の標準包含に厳密に整合する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] {a b c : Hammock.Word}
    (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (X Y : (BarrattEccles.operad A).Algebra) :
    BarrattEccles.algebraHammockGraphIntersectionComparison A f g hf hg X Y ≫
        (Subfunctor.range ((BarrattEccles.algebraHammockGraphDiagram A X Y).map f) ⊓
          Subfunctor.range ((BarrattEccles.algebraHammockGraphDiagram A X Y).map g)).ι =
      (Subfunctor.range ((BarrattEccles.algebraHammockGraphDiagram A X Y).map
        (Hammock.Word.intersectionInclusion f g))).ι :=
  BarrattEccles.algebraHammockGraphIntersectionComparison_fac A f g hf hg X Y

-- 任意の可換環上・全次数で元の有限回の縮約から縮約済みの代表へ到達する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) (r : BarrattEccles.algebraHammockRaw A X Y n) :
    ∃ s, Relation.ReflTransGen (BarrattEccles.algebraHammockRawReduction A X Y) r s ∧
      BarrattEccles.algebraHammockRawIsReduced A X Y s :=
  BarrattEccles.algebraHammockRaw_existsReducedRepresentative A X Y r

-- 元の実際の余極限内の値も、同じ縮約済みの代表へ保持される。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) (r : BarrattEccles.algebraHammockRaw A X Y n) :
    ∃ s, BarrattEccles.algebraHammockRawIsReduced A X Y s ∧
      BarrattEccles.algebraHammockRawValue A X Y r = BarrattEccles.algebraHammockRawValue A X Y s :=
  BarrattEccles.algebraHammockRaw_existsReducedSameValue A X Y r

-- 両基本縮約とも元の長さを厳密に減らす。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) {r s : BarrattEccles.algebraHammockRaw A X Y n}
    (h : BarrattEccles.algebraHammockRawReduction A X Y r s) : s.1.length < r.1.length :=
  BarrattEccles.algebraHammockRawReduction_length_lt A X Y h

-- 元の二操作の縮約関係は、全 face・degeneracy で保存される。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    {n m : SimplexCategoryᵒᵖ} {r s : BarrattEccles.algebraHammockRaw A X Y n}
    (h : BarrattEccles.algebraHammockRawReduction A X Y r s) (α : n ⟶ m) :
    BarrattEccles.algebraHammockRawReduction A X Y (BarrattEccles.algebraHammockRawMap A X Y α r)
      (BarrattEccles.algebraHammockRawMap A X Y α s) :=
  BarrattEccles.algebraHammockRawReduction_map A X Y h α

-- 元の恒等列の削除は、包含後に同じ元の全射列を厳密に回収する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] (X Y : C) {w : Word} (j : Fin w.length) (n : SimplexCategoryᵒᵖ)
    (τ : (graph W w X Y).obj n) (hτ : ∀ k, IdentityColumn (τ.obj k) j) :
    ((graphDiagram W X Y).map (Word.eraseInclusion w j)).app n
        (eraseSimplex W X Y j τ hτ) = τ := eraseSimplex_fac W X Y j τ hτ

-- 同方向二列の合成の fiber は、元の隣接二列そのもの。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {n : ℕ} (d : Fin (n + 2) → Direction) (p : Fin (n + 1))
    (hp : d p.castSucc = d p.succ) (j : Fin (n + 2)) :
    (Word.mergeMap d p hp).orderHom j = p ↔ j = p.castSucc ∨ j = p.succ :=
  Word.mergeMap_fiber d p hp j

-- 未縮約単体集合の元の射は、同じ元の余極限の値を全次数で回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) (r : BarrattEccles.algebraHammockRaw A X Y n) :
    (BarrattEccles.algebraHammockRawAugmentation A X Y).app n r =
      BarrattEccles.algebraHammockRawValue A X Y r :=
  BarrattEccles.algebraHammockRawAugmentation_app A X Y n r

-- 任意の可換環上・全次数で二つの削除は各側0〜1段の共通対象を持つ。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    {w : Hammock.Word} (n : SimplexCategoryᵒᵖ) (τ : (BarrattEccles.algebraHammockGraph A w X Y).obj n)
    (j k : Fin w.length) (hj : ∀ r, Hammock.IdentityColumn (τ.obj r) j)
    (hk : ∀ r, Hammock.IdentityColumn (τ.obj r) k) :
    ∃ q : BarrattEccles.algebraHammockRaw A X Y n,
      Relation.ReflGen (BarrattEccles.algebraHammockRawReduction A X Y)
        (BarrattEccles.algebraHammockEraseRaw A X Y j τ hj) q ∧
      Relation.ReflGen (BarrattEccles.algebraHammockRawReduction A X Y)
        (BarrattEccles.algebraHammockEraseRaw A X Y k τ hk) q :=
  BarrattEccles.algebraHammockEraseErase_join A X Y τ j k hj hk

-- 元の削除そのものが、構成済みの同じ基本縮約関係に入る。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    {w : Hammock.Word} (j : Fin w.length) (n : SimplexCategoryᵒᵖ)
    (τ : (BarrattEccles.algebraHammockGraph A w X Y).obj n)
    (hτ : ∀ r, Hammock.IdentityColumn (τ.obj r) j) :
    BarrattEccles.algebraHammockRawReduction A X Y ⟨w, τ⟩
      (BarrattEccles.algebraHammockEraseRaw A X Y j τ hτ) :=
  BarrattEccles.algebraHammockEraseRaw_reduction A X Y j τ hτ

-- 同じ元の包含後に、同じ元の全射列を厳密に回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A] (X Y : (BarrattEccles.operad A).Algebra)
    {w : Hammock.Word} (j : Fin w.length) (n : SimplexCategoryᵒᵖ)
    (τ : (BarrattEccles.algebraHammockGraph A w X Y).obj n)
    (hτ : ∀ r, Hammock.IdentityColumn (τ.obj r) j) :
    (BarrattEccles.algebraHammockGraphMap A (Hammock.Word.eraseInclusion w j) X Y).app n
      (BarrattEccles.algebraHammockEraseSimplex A X Y j τ hτ) = τ :=
  BarrattEccles.algebraHammockEraseSimplex_fac A X Y j τ hτ

-- 同じ列の像を持つ二つの包含は、元の語の等式を含めて一意。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b c : Word} (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (hfg : Set.range f.orderHom = Set.range g.orderHom) :
    ∃ hab : a = b, eqToHom hab ≫ g = f := Word.embedding_eq_of_range f g hf hg hfg

-- 元の包含の像の位置での恒等列の条件は、元の列の条件と同値。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] {W : MorphismProperty C}
    [W.IsMultiplicative] {a b : Word} {X Y : C} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) (S : Zigzag W a X Y) (i : Fin a.length) :
    IdentityColumn (WordAction.obj f S) (f.orderHom i) ↔ IdentityColumn S i :=
  identityColumn_obj_image_iff f hf S i

-- 元の二つの全射は、終域の色と語の等式も含めて比較する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b c : Word} (f : a ⟶ b) (g : a ⟶ c)
    (hf : Function.Surjective f.orderHom) (hn : b.length = c.length)
    (hfg : ∀ i, Fin.cast hn (f.orderHom i) = g.orderHom i) :
    ∃ hbc : b = c, f ≫ eqToHom hbc = g := Word.target_eq_of_surjective f g hf hn hfg

-- 三列の接した合成でも、元の二重全射は同じ列の写像を与える。
open SerrePositivity.EInfinity.Hammock in
example (x : Fin 3) :
    (0 : Fin 1).predAbove ((0 : Fin 2).predAbove x) =
      (0 : Fin 1).predAbove ((1 : Fin 2).predAbove x) :=
  Word.merge_predAbove_comp (0 : Fin 1) 0 (by decide) x

-- 任意の可換環上の元の合成同士の合流。モデル構造などの追加入力は不要。
open SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) {k : ℕ}
    (d : Fin (k + 2) → Hammock.Direction) (p q : Fin (k + 1))
    (hp : d p.castSucc = d p.succ) (hq : d q.castSucc = d q.succ)
    {n : SimplexCategoryᵒᵖ}
    (τ : (BarrattEccles.algebraHammockGraph A (⟨k + 2, d⟩ : Hammock.Word) X Y).obj n) :
    ∃ r : BarrattEccles.algebraHammockRaw A X Y n,
      Relation.ReflGen (BarrattEccles.algebraHammockRawReduction A X Y)
        (BarrattEccles.algebraHammockMergeRaw A X Y d p hp τ) r ∧
      Relation.ReflGen (BarrattEccles.algebraHammockRawReduction A X Y)
        (BarrattEccles.algebraHammockMergeRaw A X Y d q hq τ) r :=
  BarrattEccles.algebraHammockMergeMerge_join A X Y d p q hp hq τ

-- 同じ元の始域から出る二つの基本縮約は、全次数で各側0〜1段の共通対象を持つ。
open SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) {n : SimplexCategoryᵒᵖ}
    {r s t : BarrattEccles.algebraHammockRaw A X Y n}
    (hs : BarrattEccles.algebraHammockRawReduction A X Y r s)
    (ht : BarrattEccles.algebraHammockRawReduction A X Y r t) :
    ∃ q, Relation.ReflGen (BarrattEccles.algebraHammockRawReduction A X Y) s q ∧
      Relation.ReflGen (BarrattEccles.algebraHammockRawReduction A X Y) t q :=
  BarrattEccles.algebraHammockRawReduction_local_join A X Y hs ht

-- 同じ元の対象から到達した縮約済みの二つの代表は、語も含めて等しい。
open SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) {n : SimplexCategoryᵒᵖ}
    {r s t : BarrattEccles.algebraHammockRaw A X Y n}
    (hs : Relation.ReflTransGen (BarrattEccles.algebraHammockRawReduction A X Y) r s)
    (ht : Relation.ReflTransGen (BarrattEccles.algebraHammockRawReduction A X Y) r t)
    (hsr : BarrattEccles.algebraHammockRawIsReduced A X Y s)
    (htr : BarrattEccles.algebraHammockRawIsReduced A X Y t) : s = t :=
  BarrattEccles.algebraHammockReducedRepresentative_unique A X Y hs ht hsr htr

-- 元の有限縮約による正規化は、全作用素の後の再縮約に整合する。
open SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (r : BarrattEccles.algebraHammockRaw A X Y n) :
    BarrattEccles.algebraHammockNormalForm A X Y
        (BarrattEccles.algebraHammockRawMap A X Y α
          (BarrattEccles.algebraHammockNormalForm A X Y r)) =
      BarrattEccles.algebraHammockNormalForm A X Y (BarrattEccles.algebraHammockRawMap A X Y α r) :=
  BarrattEccles.algebraHammockNormalForm_map A X Y α r

-- 再縮約した単体集合の元の標準射は、元の未縮約の標準射を回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    BarrattEccles.algebraHammockNormalization A X Y ≫
        BarrattEccles.algebraHammockReducedAugmentation A X Y =
      BarrattEccles.algebraHammockRawAugmentation A X Y :=
  BarrattEccles.algebraHammockNormalization_augmentation A X Y

-- 合成する二列の一方を削除する場合、結果は元の raw の対象として既に等しい。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {C : Type e2ComplexLimitUniverse} [Category C] (W : MorphismProperty C)
    [W.IsMultiplicative] (X Y : C) {k : ℕ} (d : Fin (k + 2) → Direction)
    (p : Fin (k + 1)) (hp : d p.castSucc = d p.succ) {n : SimplexCategoryᵒᵖ}
    (τ : (graph W (⟨k + 2, d⟩ : Word) X Y).obj n)
    (hτ : ∀ r, IdentityColumn (τ.obj r) p.succ) :
    (⟨Word.mergeTarget d p, ((graphDiagram W X Y).map (Word.mergeMap d p hp)).app n τ⟩ :
      RawHammock W X Y n) =
        ⟨Word.erase (⟨k + 2, d⟩ : Word) p.succ, eraseSimplex W X Y p.succ τ hτ⟩ :=
  merge_erase_overlap_eq W X Y d p hp p.succ (Or.inr rfl) τ hτ

-- 任意の元の語の写像は、任意可換環上で同じ元の正規形を与える。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) {a b : Hammock.Word} (f : a ⟶ b)
    {n : SimplexCategoryᵒᵖ} (τ : (BarrattEccles.algebraHammockGraph A a X Y).obj n) :
    BarrattEccles.algebraHammockNormalForm A X Y
        ⟨b, (BarrattEccles.algebraHammockGraphMap A f X Y).app n τ⟩ =
      BarrattEccles.algebraHammockNormalForm A X Y ⟨a, τ⟩ :=
  BarrattEccles.algebraHammockNormalForm_transition A X Y f τ

-- 元の標準射の後の実同型は、同じ固定語の元の正規化そのもの。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (w : Hammock.Word) :
    BarrattEccles.algebraHammockGraphInclusion A w X Y ≫
        (BarrattEccles.algebraHammockReducedColimitIso A X Y).hom =
      BarrattEccles.algebraHammockGraphNormalization A X Y w :=
  BarrattEccles.algebraHammockReducedColimitIso_hom_fac A X Y w

-- 逆射も元の縮約済み対象の同じ標準射であり、任意の同型で代用しない。
open SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    (BarrattEccles.algebraHammockReducedColimitIso A X Y).inv =
      BarrattEccles.algebraHammockReducedAugmentation A X Y :=
  BarrattEccles.algebraHammockReducedColimitIso_inv A X Y

-- 元の raw 正規化は、同じ元の余極限の標準射から回収される。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) :
    BarrattEccles.algebraHammockRawAugmentation A X Y ≫
        BarrattEccles.algebraHammockColimitNormalization A X Y =
      BarrattEccles.algebraHammockNormalization A X Y :=
  BarrattEccles.algebraHammockRawAugmentation_colimitNormalization A X Y

-- 任意の元の語の射を保持した長さ段階の標準射。単射だけに制限しない。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example (F : Word ⥤ SSet.{e2ComplexLimitUniverse}) (n : ℕ) {a b : Word}
    (ha : a.length ≤ n) (hb : b.length ≤ n) (f : a ⟶ b) :
    F.map f ≫ lengthStageInclusion F n b hb = lengthStageInclusion F n a ha :=
  lengthStageInclusion_naturality F n ha hb f

-- 長さ濾過の同型は、元の余極限の比較射そのものを回収する。
open CategoryTheory CategoryTheory.Limits SerrePositivity.EInfinity.Hammock in
example {F G : Word ⥤ SSet.{e2ComplexLimitUniverse}} (η : F ⟶ G) :
    colim.map (lengthDiagramMap η) ≫ (lengthColimitIso G).hom =
      (lengthColimitIso F).hom ≫ colim.map η := lengthColimitIso_naturality η

-- 任意の可換環上で、長さ濾過の元の標準射は同じ全語の標準射になる。
open CategoryTheory CategoryTheory.Limits SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (n : ℕ) (a : Hammock.Word) (ha : a.length ≤ n) :
    BarrattEccles.algebraHammockLengthStageInclusion A X Y n a ha ≫
        colimit.ι (BarrattEccles.algebraHammockLengthDiagram A X Y) n ≫
          (BarrattEccles.algebraHammockLengthColimitIso A X Y).hom =
      BarrattEccles.algebraHammockGraphInclusion A a X Y :=
  BarrattEccles.algebraHammockLengthColimitIso_word_fac A X Y n a ha

-- 同じ長さ段階から縮約 hammock への同型は、元の正規化を回収する。
open CategoryTheory CategoryTheory.Limits SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (n : ℕ) (a : Hammock.Word) (ha : a.length ≤ n) :
    BarrattEccles.algebraHammockLengthStageInclusion A X Y n a ha ≫
        colimit.ι (BarrattEccles.algebraHammockLengthDiagram A X Y) n ≫
          (BarrattEccles.algebraHammockLengthReducedIso A X Y).hom =
      BarrattEccles.algebraHammockGraphNormalization A X Y a :=
  BarrattEccles.algebraHammockLengthReducedIso_word_fac A X Y n a ha

-- 正の長さの二つの交互方向語は異なり、空語を含む全交互方向語を分類する。
open SerrePositivity.EInfinity.Hammock in
example (n : ℕ) : Word.alternating (n + 1) .forward ≠ Word.alternating (n + 1) .backward :=
  Word.alternating_ne n
open SerrePositivity.EInfinity.Hammock in
example (a : Word) (ha : Word.IsAlternating a) :
    a = Word.alternating a.length .forward ∨ a = Word.alternating a.length .backward :=
  Word.alternating_cases a ha

-- proper の原像の重なりは、元の短い語の段階で同じ像を与える。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {F : Word ⥤ SSet.{e2ComplexLimitUniverse}} (hF : ProperDiagram F)
    {a b c : Word} (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (n : ℕ) (ha : a.length ≤ n) (hb : b.length ≤ n) (k : SimplexCategoryᵒᵖ)
    (σ : (F.obj a).obj k) (τ : (F.obj b).obj k)
    (hστ : (F.map f).app k σ = (F.map g).app k τ) :
    (lengthStageInclusion F n a ha).app k σ = (lengthStageInclusion F n b hb).app k τ :=
  hF.overlap_lengthStage f g hf hg n ha hb k σ τ hστ

-- 任意の可換環上の元の境界の射は、上の段階への元の標準射と可換。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) {n m : ℕ} (h : n ≤ m)
    (c : Hammock.Word) (hc : c.length ≤ m) :
    BarrattEccles.algebraHammockLengthBoundaryToStage A X Y n c ≫
        BarrattEccles.algebraHammockLengthTransition A X Y h =
      (BarrattEccles.algebraHammockLengthBoundary A X Y n c).ι ≫
        BarrattEccles.algebraHammockLengthStageInclusion A X Y m c hc :=
  BarrattEccles.algebraHammockLengthBoundary_square A X Y h c hc

-- 境界の表示の選択によらず、元の短い語の同じ標準射を回収する。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (n : ℕ) (c : Hammock.Word)
    (k : SimplexCategoryᵒᵖ)
    (x : ((BarrattEccles.algebraHammockLengthBoundary A X Y n c).toFunctor).obj k)
    {a : Hammock.Word} (ha : a.length ≤ n) (f : a ⟶ c) (hf : Function.Injective f.orderHom)
    (σ : (BarrattEccles.algebraHammockGraph A a X Y).obj k)
    (hσ : (BarrattEccles.algebraHammockGraphMap A f X Y).app k σ = x.val) :
    (BarrattEccles.algebraHammockLengthBoundaryToStage A X Y n c).app k x =
      (BarrattEccles.algebraHammockLengthStageInclusion A X Y n a ha).app k σ :=
  BarrattEccles.algebraHammockLengthBoundaryToStage_app A X Y n c k x ha f hf σ hσ

-- 前段階と交互方向の最大語だけの元の包含は Final。大域 instance は不要。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example (n : ℕ) : (Word.topStageInclusion n).Final := Word.topStageFinal n

-- 元の包含による同型は、同じ固定語の段階の標準射を回収する。
open CategoryTheory CategoryTheory.Limits SerrePositivity.EInfinity.Hammock in
example (F : Word ⥤ SSet.{e2ComplexLimitUniverse}) (n : ℕ) (a : Word.TopStage n) :
    colimit.ι (topStageDiagram F n) a ≫ (topStageColimitIso F n).hom =
      lengthStageInclusion F n a.obj.obj a.obj.property := topStageColimitIso_fac F n a

-- 元の列の像への分解は全射・単射を持ち、元の射と長さの上限を回収する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {a b : Word} (f : a ⟶ b) :
    Function.Surjective (Word.toImage f).orderHom ∧
      Function.Injective (Word.imageInclusion f).orderHom ∧
      Word.toImage f ≫ Word.imageInclusion f = f ∧ (Word.imageWord f).length ≤ a.length :=
  ⟨Word.toImage_surjective f, Word.imageInclusion_injective f,
    Word.toImage_fac f, Word.imageWord_length_le f⟩

-- 任意の可換環上の同じ元の段階の図式から、元の全語の標準射を回収する。
open CategoryTheory CategoryTheory.Limits SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (n : ℕ) (a : Hammock.Word.TopStage n) :
    (colimit.ι (BarrattEccles.algebraHammockTopStageDiagram A X Y n) a ≫
        (BarrattEccles.algebraHammockTopStageColimitIso A X Y n).hom) ≫
          BarrattEccles.algebraHammockLengthStageToColimit A X Y n =
      BarrattEccles.algebraHammockGraphInclusion A a.obj.obj X Y :=
  BarrattEccles.algebraHammockTopStageColimitIso_toColimit_fac A X Y n a

-- 元の最大交互語の型は有限。追加の有限性やモデル構造の仮定は不要。
open SerrePositivity.EInfinity.Hammock in
example (n : ℕ) : Finite (Word.MaximalAlternating n) := Word.maximalAlternating_finite n

-- 整合する元のデータの延長は、前段階と元の各最大語の標準射を回収する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {F : Word ⥤ SSet.{e2ComplexLimitUniverse}} {hF : ProperDiagram F} {n : ℕ}
    {Z : SSet.{e2ComplexLimitUniverse}} (d : StageAttachmentData hF n Z) :
    lengthStageTransition F (Nat.le_succ n) ≫ stageAttachmentDesc d = d.lower ∧
      ∀ a : Word.MaximalAlternating n,
        lengthStageInclusion F (n + 1) a.val a.property.1.le ≫ stageAttachmentDesc d = d.upper a :=
  ⟨stageAttachmentDesc_lower d, stageAttachmentDesc_upper d⟩

-- 元の全ての貼り合わせデータへの普遍性。値だけの一致では代用しない。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {F : Word ⥤ SSet.{e2ComplexLimitUniverse}} {hF : ProperDiagram F} {n : ℕ}
    {Z : SSet.{e2ComplexLimitUniverse}} (d : StageAttachmentData hF n Z)
    (f : lengthStage F (n + 1) ⟶ Z)
    (hl : lengthStageTransition F (Nat.le_succ n) ≫ f = d.lower)
    (hu : ∀ a : Word.MaximalAlternating n,
      lengthStageInclusion F (n + 1) a.val a.property.1.le ≫ f = d.upper a) :
    f = stageAttachmentDesc d := stageAttachmentDesc_unique d f hl hu

-- 境界への同じ持ち上げは元の包含と元の前段階の標準射を回収する。
open CategoryTheory SerrePositivity.EInfinity.Hammock in
example {F : Word ⥤ SSet.{e2ComplexLimitUniverse}} (hF : ProperDiagram F)
    (n : ℕ) {a c : Word} (ha : a.length ≤ n) (f : a ⟶ c) (hf : Function.Injective f.orderHom) :
    lengthBoundaryLift F n ha f hf ≫ (lengthBoundary F n c).ι = F.map f ∧
      lengthBoundaryLift F n ha f hf ≫ lengthBoundaryToStage hF n c =
        lengthStageInclusion F n a ha :=
  ⟨lengthBoundaryLift_ι F n ha f hf, lengthBoundaryLift_toStage F n ha f hf hF⟩

-- 任意の可換環上の実際の元の次段階の pushout。追加入力はない。
open CategoryTheory SerrePositivity.EInfinity in
example (A : Type e2ComplexLimitUniverse) [CommRing A]
    (X Y : (BarrattEccles.operad A).Algebra) (n : ℕ) :
    IsPushout (BarrattEccles.algebraHammockStageBoundaryAttach A X Y n)
      (BarrattEccles.algebraHammockStageBoundarySumInclusion A X Y n)
      (BarrattEccles.algebraHammockLengthTransition A X Y (Nat.le_succ n))
      (BarrattEccles.algebraHammockStageTopInclusion A X Y n) :=
  BarrattEccles.algebraHammockLengthStage_isPushout A X Y n
