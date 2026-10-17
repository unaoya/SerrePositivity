import SerrePositivity.InfinityCategories.DGNerve
/-!
# dg nerve の公開宣言の公理監査

概要：N0 の既存則と N1〜N7 の実装済みの全ての明示的な公開宣言を監査する。
方針：各工程で公開宣言の公理表示と型の検査を追加する。
規約：許される公理は propext・Classical.choice・Quot.sound のみ。
使われ方：対象ビルド後に `lake env lean scripts/audit_dg_nerve.lean` を実行する。
原典：HA Construction 1.3.1.6、Proposition 1.3.1.10。
dg nerve と内部ホーン充填および quasicategory instance を監査する。
ホモトピー圏と H⁰ の比較、右 pinched Hom の線形表示・加群構造・Kan 性・π₀ 比較、
一点 dg 圏と非有界複体 dg 圏の N6 の具体例、N7b の零始対象・零終対象も監査する。
-/

noncomputable section

#print axioms SerrePositivity.DifferentialGraded.differential_compose
#print axioms SerrePositivity.DifferentialGraded.compose_assoc
#print axioms SerrePositivity.DifferentialGraded.differential_unit
#print axioms SerrePositivity.DifferentialGraded.compose_unit
#print axioms SerrePositivity.DifferentialGraded.unit_compose
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.zero_compose
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_unit_of_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.unit_compose_of_heq
#print axioms SerrePositivity.InfinityCategories.dgNerve
#print axioms SerrePositivity.InfinityCategories.dgNerve.obj
#print axioms SerrePositivity.InfinityCategories.dgNerve.vertexEquiv
#print axioms SerrePositivity.InfinityCategories.dgNerve.edgeEquiv
#print axioms SerrePositivity.InfinityCategories.dgNerve.δ_obj
#print axioms SerrePositivity.InfinityCategories.dgNerve.σ_obj
#print axioms SerrePositivity.InfinityCategories.dgNerve.δ_data
#print axioms SerrePositivity.InfinityCategories.dgNerve.σ_data
#print axioms SerrePositivity.InfinityCategories.dgNerve.δ_hom
#print axioms SerrePositivity.InfinityCategories.dgNerve.σ_hom_of_inj
#print axioms SerrePositivity.InfinityCategories.dgNerve.σ_hom_eq_zero
#print axioms SerrePositivity.InfinityCategories.dgNerve.σ_hom_of_collapsed_pair
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_collision_away
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_terms_cancel
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_rhs_of_interior
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_term_of_min
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_term_of_max
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_rhs_of_collision
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.predAbove_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.degeneracy
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.three_le_card
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_of_not_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_of_not_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_iff
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_image_erase
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_sign_card
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.not_injOn_of_equal
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.erase_three_of_internal
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_left_of_min
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_right_of_min
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_right_of_max
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_left_of_max
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.nonempty
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.two_le_card
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.erase_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.erase_min
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.erase_max
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.left_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.right_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.left_min
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.left_max
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.right_min
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.right_max
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.split_card
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.eq_pair
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_min
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_max
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_erase
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_le_iff
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_lt_iff
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.collapse_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_strict_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.image_sign_card
#print axioms SerrePositivity.InfinityCategories.DGNerve.two_eq_univ
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofEdge
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle_ofEdge
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge_edgeCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeClosed
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.exists_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_data
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_of_card_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_rhs_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullbackOfInjective
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_card_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_not_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_collapsed_pair
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomFamily
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.term
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.ext
#print axioms SerrePositivity.InfinityCategories.DGNerve.zero_hom_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ext
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.vertexEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_edgeHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.TriangleData
#print axioms SerrePositivity.InfinityCategories.DGNerve.three_eq_univ
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.edgeHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofTriangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.toTriangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.toTriangle_ofTriangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle_toTriangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleEquiv
#print axioms SerrePositivity.InfinityCategories.dgNerve.triangleEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_add_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_add_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_sub_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_sub_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_units_smul_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_units_smul_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornIndex.exists_covering_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace_ne
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace_notMem
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornIndex.image_preimage
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornIndex.card_preimage
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornFaces.map_cell
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornFaces.map_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornFaces.restriction_from_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornFaces.restriction_independent
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.map_const_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.face_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.componentOnFace
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.componentOnFace_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.recoverHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sign
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.right_filter_erase_le
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.right_card_erase_lt
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sign_erase_of_lt
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sign_erase_swap
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.double_erase_pair
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sum_double_erase
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sign_right_cut
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.right_cut_card
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.left_right_sign_card
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sign_double_cut
#print axioms SerrePositivity.InfinityCategories.DGNerve.differential_squared
#print axioms SerrePositivity.InfinityCategories.DGNerve.differential_add
#print axioms SerrePositivity.InfinityCategories.DGNerve.differential_sub
#print axioms SerrePositivity.InfinityCategories.DGNerve.differential_units_smul
#print axioms SerrePositivity.InfinityCategories.DGNerve.differential_sum
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual_eq_zero_iff
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_residual
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.residual_eq_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornEquation.sum_missingComponent
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomFamily.heq_of_pointwise
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.hom_heq_of_indices
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.hom_heq_of_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.hom_heq_of_pullback_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.face_hom_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.recoverHom_heq_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.knownData
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.image_known
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_hom_heq_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_equation_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_hom_same
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_hom_of_ne
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_pullback_of_omits
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_self
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_replace_self
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.Equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.equation_image_of_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.equation_of_faces
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.replace_missing_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.replace_missing_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_of_ne
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_same
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_replace
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.correctingHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.correctingHom_self
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.solveTop
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_solveTop
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.univ_min_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.univ_max_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_known_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_top_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_top_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerOfMissingEquation
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerOfMissingEquation_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.extensionOfMissingEquation
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.interior
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.interior_erase
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sum_offDiag_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.nested_double_erase
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.homOrZero
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.homOrZero_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.linearBoundary
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.linearBoundary_squared
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.quadraticBoundary
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_eq_linear_sub_cut
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_eq_linear_sub_quadratic
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_cutCompose
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_rhs
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sign_mixed_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.mixed_right_cancel
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.mixed_left_cancel
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sum_mixed_cancel
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.sum_double_cut_cancel
#print axioms SerrePositivity.InfinityCategories.DGNerve.cubic_compose_cancel
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.residualContribution
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhsContribution
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_term
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_rhs_expansion
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_sum_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_sum_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose_erase_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose_erase_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.interior_right_cut
#print axioms SerrePositivity.InfinityCategories.DGNerve.Index.interior_left_cut
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary_linear
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.mixedBoundary_eq_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.compose_assoc_of_sum
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutRight
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutLeft
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutRight_eq_left
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary_quadratic
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cubicBoundary_eq_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhsContribution_eq_boundaries
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.sum_rhsContribution_eq_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.bianchi
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual_zero_of_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.residualContribution_of_cuts
#print axioms SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_missing_equation
#print axioms SerrePositivity.InfinityCategories.dgNerve.filler
#print axioms SerrePositivity.InfinityCategories.dgNerve.filler_face
#print axioms SerrePositivity.InfinityCategories.dgNerve.hornFilling
#print axioms SerrePositivity.InfinityCategories.dgNerve.instQuasicategory
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.pairObj
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_target_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_edgeOfCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle_edgeCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycleEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.tripleObj
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face01
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face12
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face02
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopy_of_compStruct
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStruct_iff_homotopy
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_cycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosedEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.castCycle_val_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_val_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicL_iff_exists
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicR_iff_exists
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.boundary_iff_exists
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicL_iff_boundary
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicR_iff_boundary
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.closedHom_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.closedHom_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictComp
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_strictComp
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictCompStruct
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.comp_homotopic_strictComp
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.nerveHomotopyCategory
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_homMk
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_faithful
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_full
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_essSurj
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_isEquivalence
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.equivalence
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.fromH0
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.counitIso
#print axioms SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.unitIso
#print axioms SerrePositivity.InfinityCategories.DGNerve.map_differential
#print axioms SerrePositivity.InfinityCategories.DGNerve.map_compose
#print axioms SerrePositivity.InfinityCategories.DGNerve.map_unit_of_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.map
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_term
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_rhs
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.map
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_pullback
#print axioms SerrePositivity.InfinityCategories.dgNerve.map
#print axioms SerrePositivity.InfinityCategories.dgNerve.map_id
#print axioms SerrePositivity.InfinityCategories.dgNerve.map_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.fullOnObjects
#print axioms SerrePositivity.InfinityCategories.DGNerve.liftToFull
#print axioms SerrePositivity.InfinityCategories.DGNerve.map_inclusion_lift
#print axioms SerrePositivity.InfinityCategories.DGNerve.range_inclusion

#check @SerrePositivity.InfinityCategories.DGNerve.compose_zero
#check @SerrePositivity.InfinityCategories.DGNerve.zero_compose
#check @SerrePositivity.InfinityCategories.DGNerve.compose_unit_of_heq
#check @SerrePositivity.InfinityCategories.DGNerve.unit_compose_of_heq
#check @SerrePositivity.InfinityCategories.dgNerve
#check @SerrePositivity.InfinityCategories.dgNerve.obj
#check @SerrePositivity.InfinityCategories.dgNerve.vertexEquiv
#check @SerrePositivity.InfinityCategories.dgNerve.edgeEquiv
#check @SerrePositivity.InfinityCategories.dgNerve.δ_obj
#check @SerrePositivity.InfinityCategories.dgNerve.σ_obj
#check @SerrePositivity.InfinityCategories.dgNerve.δ_data
#check @SerrePositivity.InfinityCategories.dgNerve.σ_data
#check @SerrePositivity.InfinityCategories.dgNerve.δ_hom
#check @SerrePositivity.InfinityCategories.dgNerve.σ_hom_of_inj
#check @SerrePositivity.InfinityCategories.dgNerve.σ_hom_eq_zero
#check @SerrePositivity.InfinityCategories.dgNerve.σ_hom_of_collapsed_pair
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_collision_away
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_terms_cancel
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_rhs_of_interior
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_term_of_min
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_term_of_max
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.predAbove_rhs_of_collision
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.predAbove_equation
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.degeneracy
#check @SerrePositivity.InfinityCategories.DGNerve.Index.three_le_card
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_of_not_left
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_of_not_right
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_injOn_iff
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_image_erase
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_sign_card
#check @SerrePositivity.InfinityCategories.DGNerve.Index.not_injOn_of_equal
#check @SerrePositivity.InfinityCategories.DGNerve.Index.erase_three_of_internal
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_left_of_min
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_right_of_min
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_right_of_max
#check @SerrePositivity.InfinityCategories.DGNerve.Index.predAbove_left_of_max
#check @SerrePositivity.InfinityCategories.DGNerve.Index.nonempty
#check @SerrePositivity.InfinityCategories.DGNerve.Index.two_le_card
#check @SerrePositivity.InfinityCategories.DGNerve.Index.erase_two
#check @SerrePositivity.InfinityCategories.DGNerve.Index.erase_min
#check @SerrePositivity.InfinityCategories.DGNerve.Index.erase_max
#check @SerrePositivity.InfinityCategories.DGNerve.Index.left_two
#check @SerrePositivity.InfinityCategories.DGNerve.Index.right_two
#check @SerrePositivity.InfinityCategories.DGNerve.Index.left_min
#check @SerrePositivity.InfinityCategories.DGNerve.Index.left_max
#check @SerrePositivity.InfinityCategories.DGNerve.Index.right_min
#check @SerrePositivity.InfinityCategories.DGNerve.Index.right_max
#check @SerrePositivity.InfinityCategories.DGNerve.Index.split_card
#check @SerrePositivity.InfinityCategories.DGNerve.Index.eq_pair
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_min
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_max
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_two
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_erase
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_le_iff
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_lt_iff
#check @SerrePositivity.InfinityCategories.DGNerve.Index.collapse_two
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_left
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_right
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_strict_right
#check @SerrePositivity.InfinityCategories.DGNerve.Index.image_sign_card
#check @SerrePositivity.InfinityCategories.DGNerve.two_eq_univ
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofEdge
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle_ofEdge
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge_edgeCycle
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeClosed
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleHom
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.exists_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_data
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_id
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_comp
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_of_card_two
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_rhs_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullbackOfInjective
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_card_two
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_not_inj
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_collapsed_pair
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_id
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_comp
#check @SerrePositivity.InfinityCategories.DGNerve.HomFamily
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.term
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.ext
#check @SerrePositivity.InfinityCategories.DGNerve.zero_hom_heq
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ext
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.vertex
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.vertexEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeHom
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_edgeHom
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle
#check @SerrePositivity.InfinityCategories.DGNerve.TriangleData
#check @SerrePositivity.InfinityCategories.DGNerve.three_eq_univ
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.edgeHom
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_triangle
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofTriangle
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.toTriangle
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.toTriangle_ofTriangle
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ofTriangle_toTriangle
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleEquiv
#check @SerrePositivity.InfinityCategories.dgNerve.triangleEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.compose_add_left
#check @SerrePositivity.InfinityCategories.DGNerve.compose_add_right
#check @SerrePositivity.InfinityCategories.DGNerve.compose_sub_left
#check @SerrePositivity.InfinityCategories.DGNerve.compose_sub_right
#check @SerrePositivity.InfinityCategories.DGNerve.compose_units_smul_left
#check @SerrePositivity.InfinityCategories.DGNerve.compose_units_smul_right
#check @SerrePositivity.InfinityCategories.DGNerve.HornIndex.exists_covering_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace
#check @SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace_ne
#check @SerrePositivity.InfinityCategories.DGNerve.HornIndex.coveringFace_notMem
#check @SerrePositivity.InfinityCategories.DGNerve.HornIndex.image_preimage
#check @SerrePositivity.InfinityCategories.DGNerve.HornIndex.card_preimage
#check @SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell
#check @SerrePositivity.InfinityCategories.DGNerve.HornFaces.cell_eq
#check @SerrePositivity.InfinityCategories.DGNerve.HornFaces.map_cell
#check @SerrePositivity.InfinityCategories.DGNerve.HornFaces.map_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornFaces.restriction_from_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornFaces.restriction_independent
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.map_const_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.vertexObj
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.face_obj
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.componentOnFace
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.componentOnFace_heq
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.recoverHom
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sign
#check @SerrePositivity.InfinityCategories.DGNerve.Index.right_filter_erase_le
#check @SerrePositivity.InfinityCategories.DGNerve.Index.right_card_erase_lt
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sign_erase_of_lt
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sign_erase_swap
#check @SerrePositivity.InfinityCategories.DGNerve.Index.double_erase_pair
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sum_double_erase
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sign_right_cut
#check @SerrePositivity.InfinityCategories.DGNerve.Index.right_cut_card
#check @SerrePositivity.InfinityCategories.DGNerve.Index.left_right_sign_card
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sign_double_cut
#check @SerrePositivity.InfinityCategories.DGNerve.differential_squared
#check @SerrePositivity.InfinityCategories.DGNerve.differential_add
#check @SerrePositivity.InfinityCategories.DGNerve.differential_sub
#check @SerrePositivity.InfinityCategories.DGNerve.differential_units_smul
#check @SerrePositivity.InfinityCategories.DGNerve.differential_sum
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual_eq_zero_iff
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_residual
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.residual_eq_zero
#check @SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent
#check @SerrePositivity.InfinityCategories.DGNerve.HornEquation.sum_missingComponent
#check @SerrePositivity.InfinityCategories.DGNerve.HornEquation.missingComponent_eq
#check @SerrePositivity.InfinityCategories.DGNerve.HomFamily.heq_of_pointwise
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.hom_heq_of_indices
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.hom_heq_of_eq
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.hom_heq_of_pullback_eq
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.face_hom_heq
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.recoverHom_heq_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.knownData
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.image_known
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_hom_heq_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_equation_image
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.knownData_equation
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_hom_same
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_hom_of_ne
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.replace_pullback_of_omits
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_self
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_replace_self
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.Equation
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.equation_image_of_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.equation_of_faces
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.replace_missing_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.replace_missing_equation
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_of_ne
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_replace_same
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_replace
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.correctingHom
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.correctingHom_self
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.solveTop
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_solveTop
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.univ_min_zero
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.univ_max_last
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_known_equation
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_top_zero
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_top_equation
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerOfMissingEquation
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerOfMissingEquation_face
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.extensionOfMissingEquation
#check @SerrePositivity.InfinityCategories.DGNerve.Index.interior
#check @SerrePositivity.InfinityCategories.DGNerve.Index.interior_erase
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sum_offDiag_eq
#check @SerrePositivity.InfinityCategories.DGNerve.Index.nested_double_erase
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.homOrZero
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.homOrZero_eq
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.linearBoundary
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.linearBoundary_squared
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.quadraticBoundary
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_eq_linear_sub_cut
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_eq_linear_sub_quadratic
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_cutCompose
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_rhs
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sign_mixed_right
#check @SerrePositivity.InfinityCategories.DGNerve.Index.mixed_right_cancel
#check @SerrePositivity.InfinityCategories.DGNerve.Index.mixed_left_cancel
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sum_mixed_cancel
#check @SerrePositivity.InfinityCategories.DGNerve.Index.sum_double_cut_cancel
#check @SerrePositivity.InfinityCategories.DGNerve.cubic_compose_cancel
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.residualContribution
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhsContribution
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_term
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.differential_rhs_expansion
#check @SerrePositivity.InfinityCategories.DGNerve.compose_sum_left
#check @SerrePositivity.InfinityCategories.DGNerve.compose_sum_right
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose_erase_left
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutCompose_erase_right
#check @SerrePositivity.InfinityCategories.DGNerve.Index.interior_right_cut
#check @SerrePositivity.InfinityCategories.DGNerve.Index.interior_left_cut
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary_linear
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.mixedBoundary_eq_zero
#check @SerrePositivity.InfinityCategories.DGNerve.compose_assoc_of_sum
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutRight
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutLeft
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.nestedCutRight_eq_left
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutBoundary_quadratic
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cubicBoundary_eq_zero
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhsContribution_eq_boundaries
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.sum_rhsContribution_eq_zero
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.bianchi
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.residual_zero_of_equation
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.residualContribution_of_cuts
#check @SerrePositivity.InfinityCategories.DGNerve.HornData.fillerData_missing_equation
#check @SerrePositivity.InfinityCategories.dgNerve.filler
#check @SerrePositivity.InfinityCategories.dgNerve.filler_face
#check @SerrePositivity.InfinityCategories.dgNerve.hornFilling
#check @SerrePositivity.InfinityCategories.dgNerve.instQuasicategory
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.pairObj
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_source_obj
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edge_target_obj
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_edgeOfCycle
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeOfCycle_edgeCycle
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycleEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.tripleObj
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face01
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face12
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.triangle_face02
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStructOfHomotopy
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopy_of_compStruct
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.compStruct_iff_homotopy
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.vertexClosed
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_cycle
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosedEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.castCycle_val_heq
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_val_heq
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeCycle_id
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicL_iff_exists
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicR_iff_exists
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.boundary_iff_exists
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicL_iff_boundary
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.homotopicR_iff_boundary
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.closedHom_id
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.closedHom_comp
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_id
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictComp
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.edgeClosed_strictComp
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.strictCompStruct
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.comp_homotopic_strictComp
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.nerveHomotopyCategory
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_homMk
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_faithful
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_full
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_essSurj
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.toH0_isEquivalence
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.equivalence
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.fromH0
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.counitIso
#check @SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.unitIso
#check @SerrePositivity.InfinityCategories.DGNerve.map_differential
#check @SerrePositivity.InfinityCategories.DGNerve.map_compose
#check @SerrePositivity.InfinityCategories.DGNerve.map_unit_of_heq
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.map
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_term
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_rhs
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.map
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_id
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_comp
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.map_pullback
#check @SerrePositivity.InfinityCategories.dgNerve.map
#check @SerrePositivity.InfinityCategories.dgNerve.map_id
#check @SerrePositivity.InfinityCategories.dgNerve.map_comp
#check @SerrePositivity.InfinityCategories.DGNerve.fullOnObjects
#check @SerrePositivity.InfinityCategories.DGNerve.liftToFull
#check @SerrePositivity.InfinityCategories.DGNerve.map_inclusion_lift
#check @SerrePositivity.InfinityCategories.DGNerve.range_inclusion

#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.phaseObj
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.phaseObj
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_00
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_00
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_01
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_01
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_11
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_11
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_zero
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_sub
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_sub
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_smul
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_smul
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_differential
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_differential
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_compose
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_compose
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_unit
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_unit
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_sum
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_sum
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_unit_of_heq
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.transition_unit_of_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_term
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_term
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_rhs
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_rhs
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplexData_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_zero
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_one
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.simplex_one
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap_zero
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap_one
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopyMap_one
#print axioms SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopy
#check @SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans.homotopy

#print axioms SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom
#check @SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom
#print axioms SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom_castSucc
#check @SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom_castSucc
#print axioms SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom_last
#check @SerrePositivity.InfinityCategories.PinchedHom.extendOrderHom_last
#print axioms SerrePositivity.InfinityCategories.PinchedHom.extend
#check @SerrePositivity.InfinityCategories.PinchedHom.extend
#print axioms SerrePositivity.InfinityCategories.PinchedHom.front
#check @SerrePositivity.InfinityCategories.PinchedHom.front
#print axioms SerrePositivity.InfinityCategories.PinchedHom.lastVertex
#check @SerrePositivity.InfinityCategories.PinchedHom.lastVertex
#print axioms SerrePositivity.InfinityCategories.PinchedHom.front_extend
#check @SerrePositivity.InfinityCategories.PinchedHom.front_extend
#print axioms SerrePositivity.InfinityCategories.PinchedHom.lastVertex_extend
#check @SerrePositivity.InfinityCategories.PinchedHom.lastVertex_extend
#print axioms SerrePositivity.InfinityCategories.PinchedHom.extend_id
#check @SerrePositivity.InfinityCategories.PinchedHom.extend_id
#print axioms SerrePositivity.InfinityCategories.PinchedHom.extend_comp
#check @SerrePositivity.InfinityCategories.PinchedHom.extend_comp
#print axioms SerrePositivity.InfinityCategories.PinchedHom.front_eq_δ
#check @SerrePositivity.InfinityCategories.PinchedHom.front_eq_δ
#print axioms SerrePositivity.InfinityCategories.PinchedHom.front_zero
#check @SerrePositivity.InfinityCategories.PinchedHom.front_zero
#print axioms SerrePositivity.InfinityCategories.PinchedHom.lastVertex_zero
#check @SerrePositivity.InfinityCategories.PinchedHom.lastVertex_zero
#print axioms SerrePositivity.InfinityCategories.PinchedHom.constant
#check @SerrePositivity.InfinityCategories.PinchedHom.constant
#print axioms SerrePositivity.InfinityCategories.PinchedHom.constant_pullback
#check @SerrePositivity.InfinityCategories.PinchedHom.constant_pullback
#print axioms SerrePositivity.InfinityCategories.PinchedHom.Simplex
#check @SerrePositivity.InfinityCategories.PinchedHom.Simplex
#print axioms SerrePositivity.InfinityCategories.PinchedHom.Simplex.ext
#check @SerrePositivity.InfinityCategories.PinchedHom.Simplex.ext
#print axioms SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback
#check @SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback
#print axioms SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback_id
#check @SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback_id
#print axioms SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback_comp
#check @SerrePositivity.InfinityCategories.PinchedHom.Simplex.pullback_comp
#print axioms SerrePositivity.InfinityCategories.pinchedHom
#check @SerrePositivity.InfinityCategories.pinchedHom
#print axioms SerrePositivity.InfinityCategories.PinchedHom.constant_zero
#check @SerrePositivity.InfinityCategories.PinchedHom.constant_zero
#print axioms SerrePositivity.InfinityCategories.PinchedHom.vertexEquiv
#check @SerrePositivity.InfinityCategories.PinchedHom.vertexEquiv
#print axioms SerrePositivity.InfinityCategories.PinchedHom.vertexEquiv_edge
#check @SerrePositivity.InfinityCategories.PinchedHom.vertexEquiv_edge
#print axioms SerrePositivity.InfinityCategories.DGNerve.pinchedHom
#check @SerrePositivity.InfinityCategories.DGNerve.pinchedHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.vertexCycleEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.vertexCycleEquiv

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.component
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.erase_nonempty
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.erase_nonempty
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_add
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_add
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_smul
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_smul
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.linearSubmodule
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.linearSubmodule
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.equation
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.closed_singleton
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.closed_singleton
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_component_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_component_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_component_of_not_inj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_component_of_not_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_id
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_comp
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.last_not_mem_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.last_not_mem_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.two_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.two_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.max_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.max_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.source_obj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.source_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.target_obj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.target_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_component_heq
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_component_heq

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.not_injOn_constant
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.not_injOn_constant
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.constant_hom_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.constant_hom_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.constant_hom_unit
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.constant_hom_unit
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_heq
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_unit
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_unit
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.compose_front_hom_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.compose_front_hom_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.compose_front_hom_unit
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.compose_front_hom_unit
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.erase_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.erase_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.right_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.right_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_above_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_above_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second_mem_erase
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.second_mem_erase
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.first_lt_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.first_lt_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.right_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.right_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_first
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_first
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.above_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sign_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sign_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_card_two_iff
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.left_card_two_iff

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_heq_of_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_heq_of_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_zero_of_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_zero_of_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_unit_of_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.front_hom_unit_of_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.hom_heq_of_indices_degree
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.hom_heq_of_indices_degree
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutLeft
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutLeft
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutRight
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutRight
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutComposite
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.cutComposite
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.erasedComponent
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.erasedComponent
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_eq_sub_cutComposite
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.term_eq_sub_cutComposite
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_zero_of_ne_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_zero_of_ne_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutRight_second_heq_component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutRight_second_heq_component
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_second_heq_component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.cutComposite_second_heq_component
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.erasedComponent_heq_component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.erasedComponent_heq_component
#print axioms SerrePositivity.InfinityCategories.DGNerve.smul_sub_heq_of_obj_eq
#check @SerrePositivity.InfinityCategories.DGNerve.smul_sub_heq_of_obj_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.term_heq_linear
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.term_heq_linear

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLastEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLastEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_linear_terms
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_linear_terms
#print axioms SerrePositivity.InfinityCategories.DGNerve.sum_heq_of_obj_eq
#check @SerrePositivity.InfinityCategories.DGNerve.sum_heq_of_obj_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.differential_heq_of_obj_eq
#check @SerrePositivity.InfinityCategories.DGNerve.differential_heq_of_obj_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_heq_linear_terms
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_heq_linear_terms
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_heq_linear
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.rhs_heq_linear
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_equation
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearSimplex
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearSimplex

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.image_withoutLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.image_withoutLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast_withoutLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withLast_withoutLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast_withLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast_withLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_withoutLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.card_withoutLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast_nonempty
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.withoutLast_nonempty
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_ne_last
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_ne_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_withoutLast
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.min_withoutLast
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.toPinchedLinearData
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.toPinchedLinearData
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.toPinchedLinearData_component_heq
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.toPinchedLinearData_component_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_of_ne_last
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_of_ne_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_of_eq_last
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_of_eq_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_castSucc
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.reconstructObj_castSucc
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_last
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_unit
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_unit
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_hom_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_toPinchedLinearData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_toPinchedLinearData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_front
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_front
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_last
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toSimplexData_last

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.source_obj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.source_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.target_obj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.target_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_component_heq
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_component_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.ofSimplex
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.ofSimplex
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_ofSimplex
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_ofSimplex
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toLinearData_toData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.toLinearData_toData
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.data_hom_heq_of_eq
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.data_hom_heq_of_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_heq
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_heq_of_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_heq_of_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_zero_of_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_zero_of_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_unit_of_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.front_hom_unit_of_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_zero_of_ne_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_zero_of_ne_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_second
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_second
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutRight_second_heq_component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutRight_second_heq_component
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_second_heq_component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cutComposite_second_heq_component
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.erasedComponent_heq_component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.erasedComponent_heq_component
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.term_heq_linear
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.term_heq_linear
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear_terms
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear_terms
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear_all
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.rhs_heq_linear_all
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cone_equation_of_linear
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.cone_equation_of_linear
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.equation_of_indices
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.equation_of_indices
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.source_equation_on_image
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.source_equation_on_image
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.equation_of_linear
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.equation_of_linear
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toSimplex
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toSimplex
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toPinched
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toPinched
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toLinearSimplex_toPinched
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.toLinearSimplex_toPinched
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.ext
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.ext
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.hom_heq_linear_of_last
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.hom_heq_linear_of_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_injective
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data.toLinearData_injective
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toPinched_toLinearSimplex
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toPinched_toLinearSimplex
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.linearEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.linearEquiv

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.image_withLast_extend
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.image_withLast_extend
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.injOn_extend_withLast_iff
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.injOn_extend_withLast_iff
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.two_of_not_injOn
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.two_of_not_injOn
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearData_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_mem
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_mem
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_val
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_val
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_id
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_comp
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex.pullback_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearSimplex_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.toLinearSimplex_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instRawAddCommGroup
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instRawAddCommGroup
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instAddCommGroup
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instAddCommGroup
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instRawModule
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instRawModule
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instModule
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instModule
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleEquiv_apply
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleEquiv_apply
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullbackLinear
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullbackLinear
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullbackLinear_apply
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullbackLinear_apply
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullback_add
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullback_add
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullback_smul
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.pullback_smul
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleObject
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleObject
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleObject_map_apply
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.moduleObject_map_apply

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deletionSign
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deletionSign
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deletionSign_eq_neg
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deletionSign_eq_neg
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deleteSum
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deleteSum
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deleteSum_squared
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deleteSum_squared
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deletionSolution
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.deletionSolution
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_eq_zero_of_deletionSolution
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.sum_eq_zero_of_deletionSolution
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.componentOrZero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.componentOrZero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.componentOrZero_eq
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.componentOrZero_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.componentOrZero_empty
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.componentOrZero_empty
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_eq_deleteSum
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_eq_deleteSum
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.sum_rhs_eq_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.sum_rhs_eq_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.residual
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.residual
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.residual_eq_zero_iff
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.residual_eq_zero_iff
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.differential_rhs
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.differential_rhs
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.differential_rhs_residual
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.differential_rhs_residual
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.missing_equation
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.missing_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_eq_zero_of_deletionSolution
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.rhs_eq_zero_of_deletionSolution

#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_rhs_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData.pullback_rhs_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.faceData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.faceData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.face_component_eq
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.face_component_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.recoverComponent
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.recoverComponent
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.recoverComponent_eq_face
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.recoverComponent_eq_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.image_known
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.image_known
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.knownData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.knownData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.knownData_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.knownData_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.equation_of_faces
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.equation_of_faces
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_component_of_ne
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_component_of_ne
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_top_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_top_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_componentOrZero_of_ne
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_componentOrZero_of_ne
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_missing_component
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_missing_component
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_top_rhs_zero
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_top_rhs_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_missing_equation
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_missing_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_mem
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.fillerData_mem
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.filler
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.HornData.filler
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.filler
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.filler
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.filler_face
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.filler_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.hornFilling
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.hornFilling
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instKanComplex
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.instKanComplex

#print axioms SerrePositivity.InfinityCategories.PinchedHom.extend_δ_zero
#check @SerrePositivity.InfinityCategories.PinchedHom.extend_δ_zero
#print axioms SerrePositivity.InfinityCategories.PinchedHom.extend_δ_one
#check @SerrePositivity.InfinityCategories.PinchedHom.extend_δ_one
#print axioms SerrePositivity.InfinityCategories.PinchedHom.constant_one
#check @SerrePositivity.InfinityCategories.PinchedHom.constant_one
#print axioms SerrePositivity.InfinityCategories.PinchedHom.lastVertex_one
#check @SerrePositivity.InfinityCategories.PinchedHom.lastVertex_one
#print axioms SerrePositivity.InfinityCategories.PinchedHom.pathCompStruct
#check @SerrePositivity.InfinityCategories.PinchedHom.pathCompStruct
#print axioms SerrePositivity.InfinityCategories.PinchedHom.pathOfCompStruct
#check @SerrePositivity.InfinityCategories.PinchedHom.pathOfCompStruct
#print axioms SerrePositivity.InfinityCategories.PinchedHom.path_iff_compStruct
#check @SerrePositivity.InfinityCategories.PinchedHom.path_iff_compStruct
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.vertexClosedEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.vertexClosedEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.path_iff_boundary
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.path_iff_boundary
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0_mk
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0_mk
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZero_mk_eq_iff_boundary
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZero_mk_eq_iff_boundary
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0_injective
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0_injective
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0_surjective
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroToH0_surjective
#print axioms SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.PinchedHom.piZeroEquiv

#print axioms SerrePositivity.InfinityCategories.DGNerve.Checks.ring_triangle_equation
#check @SerrePositivity.InfinityCategories.DGNerve.Checks.ring_triangle_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.Checks.complex_compose
#check @SerrePositivity.InfinityCategories.DGNerve.Checks.complex_compose
#print axioms SerrePositivity.InfinityCategories.DGNerve.Checks.complex_triangle_equation
#check @SerrePositivity.InfinityCategories.DGNerve.Checks.complex_triangle_equation

#print axioms SerrePositivity.InfinityCategories.DGNerve.constantZeroFunctor
#check @SerrePositivity.InfinityCategories.DGNerve.constantZeroFunctor
#print axioms SerrePositivity.InfinityCategories.DGNerve.toZeroStrict
#check @SerrePositivity.InfinityCategories.DGNerve.toZeroStrict
#print axioms SerrePositivity.InfinityCategories.DGNerve.fromZeroStrict
#check @SerrePositivity.InfinityCategories.DGNerve.fromZeroStrict
#print axioms SerrePositivity.InfinityCategories.DGNerve.terminalPhase
#check @SerrePositivity.InfinityCategories.DGNerve.terminalPhase
#print axioms SerrePositivity.InfinityCategories.DGNerve.terminalPhase_castSucc
#check @SerrePositivity.InfinityCategories.DGNerve.terminalPhase_castSucc
#print axioms SerrePositivity.InfinityCategories.DGNerve.terminalPhase_last
#check @SerrePositivity.InfinityCategories.DGNerve.terminalPhase_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.appendZero
#check @SerrePositivity.InfinityCategories.DGNerve.appendZero
#print axioms SerrePositivity.InfinityCategories.DGNerve.appendZero_last
#check @SerrePositivity.InfinityCategories.DGNerve.appendZero_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.appendZero_front
#check @SerrePositivity.InfinityCategories.DGNerve.appendZero_front
#print axioms SerrePositivity.InfinityCategories.DGNerve.zeroGradedHom_heq
#check @SerrePositivity.InfinityCategories.DGNerve.zeroGradedHom_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ext_of_zero_last
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ext_of_zero_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face
#check @SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face
#print axioms SerrePositivity.InfinityCategories.DGNerve.BoundaryData.vertex_face
#check @SerrePositivity.InfinityCategories.DGNerve.BoundaryData.vertex_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_vertex
#check @SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_vertex
#print axioms SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_front
#check @SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_front
#print axioms SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_back
#check @SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_back
#print axioms SerrePositivity.InfinityCategories.DGNerve.δ_last_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.δ_last_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_last_obj
#check @SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_last_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.appendZero_boundary_face
#check @SerrePositivity.InfinityCategories.DGNerve.appendZero_boundary_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.isTerminalVertex_of_isZero
#check @SerrePositivity.InfinityCategories.DGNerve.isTerminalVertex_of_isZero
#print axioms SerrePositivity.InfinityCategories.DGNerve.initialPhase
#check @SerrePositivity.InfinityCategories.DGNerve.initialPhase
#print axioms SerrePositivity.InfinityCategories.DGNerve.initialPhase_succ
#check @SerrePositivity.InfinityCategories.DGNerve.initialPhase_succ
#print axioms SerrePositivity.InfinityCategories.DGNerve.initialPhase_zero
#check @SerrePositivity.InfinityCategories.DGNerve.initialPhase_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.prependZero
#check @SerrePositivity.InfinityCategories.DGNerve.prependZero
#print axioms SerrePositivity.InfinityCategories.DGNerve.prependZero_first
#check @SerrePositivity.InfinityCategories.DGNerve.prependZero_first
#print axioms SerrePositivity.InfinityCategories.DGNerve.prependZero_back
#check @SerrePositivity.InfinityCategories.DGNerve.prependZero_back
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ext_of_zero_first
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ext_of_zero_first
#print axioms SerrePositivity.InfinityCategories.DGNerve.δ_zero_pullback
#check @SerrePositivity.InfinityCategories.DGNerve.δ_zero_pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_first_obj
#check @SerrePositivity.InfinityCategories.DGNerve.BoundaryData.face_first_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.prependZero_boundary_face
#check @SerrePositivity.InfinityCategories.DGNerve.prependZero_boundary_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.isInitialVertex_of_isZero
#check @SerrePositivity.InfinityCategories.DGNerve.isInitialVertex_of_isZero
#print axioms SerrePositivity.InfinityCategories.DGNerve.isTerminalVertex_zero
#check @SerrePositivity.InfinityCategories.DGNerve.isTerminalVertex_zero
#print axioms SerrePositivity.InfinityCategories.DGNerve.isInitialVertex_zero
#check @SerrePositivity.InfinityCategories.DGNerve.isInitialVertex_zero

#print axioms SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates
#check @SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates
#print axioms SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates_symm
#check @SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates_symm
#print axioms SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates_symm_differential
#check @SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates_symm_differential
#print axioms SerrePositivity.InfinityCategories.DGNerve.complexEdge
#check @SerrePositivity.InfinityCategories.DGNerve.complexEdge
#print axioms SerrePositivity.InfinityCategories.DGNerve.complexEdge_cycle
#check @SerrePositivity.InfinityCategories.DGNerve.complexEdge_cycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.complexCompStruct
#check @SerrePositivity.InfinityCategories.DGNerve.complexCompStruct
#print axioms SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates
#check @SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates
#print axioms SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates_fst
#check @SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates_fst
#print axioms SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates_snd
#check @SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates_snd
#print axioms SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates_symm
#check @SerrePositivity.InfinityCategories.DGNerve.coneHomCoordinates_symm
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanConeTriangleLeft_first
#check @SerrePositivity.InfinityCategories.DGNerve.cospanConeTriangleLeft_first
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiberCone_vertex
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiberCone_vertex
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiber
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiber
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates
#check @SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_fst
#check @SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_fst
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_snd
#check @SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_snd
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_symm
#check @SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_symm
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_symm_differential
#check @SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_symm_differential
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberShiftCocycle_val
#check @SerrePositivity.InfinityCategories.DGNerve.fiberShiftCocycle_val
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberUnshift_eq_comp
#check @SerrePositivity.InfinityCategories.DGNerve.fiberUnshift_eq_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_fst_eq_comp
#check @SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_fst_eq_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_snd_eq_comp
#check @SerrePositivity.InfinityCategories.DGNerve.fiberHomCoordinates_snd_eq_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberShiftCocycle
#check @SerrePositivity.InfinityCategories.DGNerve.fiberShiftCocycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberProjectionCycle
#check @SerrePositivity.InfinityCategories.DGNerve.fiberProjectionCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberProjection
#check @SerrePositivity.InfinityCategories.DGNerve.fiberProjection
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberProjection_cochain
#check @SerrePositivity.InfinityCategories.DGNerve.fiberProjection_cochain
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberNullHomotopy
#check @SerrePositivity.InfinityCategories.DGNerve.fiberNullHomotopy
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberNullHomotopy_differential
#check @SerrePositivity.InfinityCategories.DGNerve.fiberNullHomotopy_differential
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberDifference
#check @SerrePositivity.InfinityCategories.DGNerve.fiberDifference
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackFiber
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackFiber
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackProjectionB
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackProjectionB
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackProjectionC
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackProjectionC
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackDiagonal
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackDiagonal
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomotopy_differential
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomotopy_differential
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberLowerTriangle
#check @SerrePositivity.InfinityCategories.DGNerve.fiberLowerTriangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.fiberUpperTriangle
#check @SerrePositivity.InfinityCategories.DGNerve.fiberUpperTriangle
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_upper
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_upper
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_lower
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_lower
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_right
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_right
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_top
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiberSquare_top
#print axioms SerrePositivity.InfinityCategories.DGNerve.standardFiberCone
#check @SerrePositivity.InfinityCategories.DGNerve.standardFiberCone
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_symm
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_symm
#print axioms SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates_comp_difference
#check @SerrePositivity.InfinityCategories.DGNerve.biproductHomCoordinates_comp_difference
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_symm_differential
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_symm_differential
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_left_eq_comp
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_left_eq_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_right_eq_comp
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_right_eq_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_homotopy_eq_comp
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomCoordinates_homotopy_eq_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomBoundaryLift
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomBoundaryLift
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomBoundaryLift_coordinates
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomBoundaryLift_coordinates
#print axioms SerrePositivity.InfinityCategories.DGNerve.pullbackHomBoundaryLift_differential
#check @SerrePositivity.InfinityCategories.DGNerve.pullbackHomBoundaryLift_differential

#print axioms SerrePositivity.InfinityCategories.DGNerve.hom_to_stdSimplex_ext_vertices
#check @SerrePositivity.InfinityCategories.DGNerve.hom_to_stdSimplex_ext_vertices
#print axioms SerrePositivity.InfinityCategories.DGNerve.join_hom_to_stdSimplex_ext
#check @SerrePositivity.InfinityCategories.DGNerve.join_hom_to_stdSimplex_ext
#print axioms SerrePositivity.InfinityCategories.DGNerve.joinLeftOrderHom
#check @SerrePositivity.InfinityCategories.DGNerve.joinLeftOrderHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.joinRightOrderHom
#check @SerrePositivity.InfinityCategories.DGNerve.joinRightOrderHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_inl
#check @SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_inl
#print axioms SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_inr
#check @SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_inr
#print axioms SerrePositivity.InfinityCategories.DGNerve.succAbove_castAdd_two
#check @SerrePositivity.InfinityCategories.DGNerve.succAbove_castAdd_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_left_face
#check @SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_left_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_right_last
#check @SerrePositivity.InfinityCategories.DGNerve.joinStdSimplexIso_right_last
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanJoinLeft
#check @SerrePositivity.InfinityCategories.DGNerve.cospanJoinLeft
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanJoinRight
#check @SerrePositivity.InfinityCategories.DGNerve.cospanJoinRight
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanJoin_isPushout
#check @SerrePositivity.InfinityCategories.DGNerve.cospanJoin_isPushout
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanJoinLeft_face
#check @SerrePositivity.InfinityCategories.DGNerve.cospanJoinLeft_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanJoinRight_face
#check @SerrePositivity.InfinityCategories.DGNerve.cospanJoinRight_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.region
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.region
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.cell
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.cell
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.cell_eq
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.cell_eq
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.map_cell
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.map_cell
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.map_face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.map_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.restriction_from_face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.restriction_from_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.restriction_independent
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.restriction_independent
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.face_hom_heq
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.face_hom_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.CoversVertices
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.CoversVertices
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.vertexCell
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.vertexCell
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.map_const_face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.map_const_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.vertexObj
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.vertexObj
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.face_obj
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.face_obj
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.componentOnFace
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.componentOnFace
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.componentOnFace_heq
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.componentOnFace_heq
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.recoverHom
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.recoverHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.recoverHom_heq_face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.recoverHom_heq_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.factor_δ_comp
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.factor_δ_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.Compatible
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.Compatible
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.descValue
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.descValue
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.descValue_cell
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.descValue_cell
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.desc
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.desc
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.factor_δ_self
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.factor_δ_self
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.desc_face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.desc_face

#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaces
#check @SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaces
#print axioms SerrePositivity.InfinityCategories.DGNerve.mem_cospanPrefixFaces
#check @SerrePositivity.InfinityCategories.DGNerve.mem_cospanPrefixFaces
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaceIndex
#check @SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaceIndex
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaceIndex_castAdd
#check @SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaceIndex_castAdd
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaces_covers
#check @SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaces_covers
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaces_known_iff
#check @SerrePositivity.InfinityCategories.DGNerve.cospanPrefixFaces_known_iff
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.compatible_of_lifts
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.compatible_of_lifts
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryInclusion
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryInclusion
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryInclusion_mono
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryInclusion_mono
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftLift
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftLift
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightLift
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightLift
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftLift_inclusion
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftLift_inclusion
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightLift_inclusion
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightLift_inclusion
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeft
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeft
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRight
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRight
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeft_face
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeft_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRight_face
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRight_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanFirstTail
#check @SerrePositivity.InfinityCategories.DGNerve.cospanFirstTail
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanLastTail
#check @SerrePositivity.InfinityCategories.DGNerve.cospanLastTail
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanVertex_cases
#check @SerrePositivity.InfinityCategories.DGNerve.cospanVertex_cases
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanUnknown_cases
#check @SerrePositivity.InfinityCategories.DGNerve.cospanUnknown_cases
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.image_known
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.image_known
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData_hom_heq_face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData_hom_heq_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.equation_of_faces
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.equation_of_faces
#print axioms SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData_equation
#check @SerrePositivity.InfinityCategories.DGNerve.SelectedFaces.assembleData_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftData
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftData
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightData
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightData
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftData_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftData_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightData_pullback_face
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightData_pullback_face
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftData_equation
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryLeftData_equation
#print axioms SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightData_equation
#check @SerrePositivity.InfinityCategories.DGNerve.cospanBoundaryRightData_equation

section
universe u v
variable (A : Type u) [CommRing A] (D : Type v)
  [SerrePositivity.DifferentialGraded.DGCategory A D]
example (x y : D) (n : ℕ) :
    Module A (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n) :=
  inferInstance
example (x y : D) (n : ℕ) :
    AddCommGroup (SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearSimplex A x y n) :=
  inferInstance
example (x y : D) (n : ℕ) :
    Module A ((SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj
      (Opposite.op (SimplexCategory.mk n))) := inferInstance
example (x y : D) (n : ℕ) :
    AddCommGroup ((SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y).obj
      (Opposite.op (SimplexCategory.mk n))) := inferInstance
example (x y : D) :
    SSet.KanComplex (SerrePositivity.InfinityCategories.DGNerve.pinchedHom A D x y) := inferInstance
example : SSet.Quasicategory (SerrePositivity.InfinityCategories.dgNerve A D) := inferInstance
example : SSet.Truncated.Quasicategory₂
    (SerrePositivity.InfinityCategories.DGNerve.HomotopyComparison.twoTruncation A D) := inferInstance
end
end
