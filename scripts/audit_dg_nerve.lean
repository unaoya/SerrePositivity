import SerrePositivity.InfinityCategories.DGNerve
/-!
# dg nerve の公開宣言の公理監査

概要：N0 の既存則と N1 と N2 途中の全ての明示的な公開宣言を監査する。
方針：各工程で公開宣言の公理表示と型の検査を追加する。
規約：許される公理は propext・Classical.choice・Quot.sound のみ。
使われ方：対象ビルド後に `lake env lean scripts/audit_dg_nerve.lean` を実行する。
原典：HA Construction 1.3.1.6、Proposition 1.3.1.10。
dg nerve は構成済み。ホーン充填の完成をこの監査から主張しない。
-/

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
