import SerrePositivity.InfinityCategories.DGNerve.LowDimensional
import SerrePositivity.InfinityCategories.DGNerve.PullbackEquation

/-!
# dg nerve の公開宣言の公理監査

概要：N0 の既存則と N1 途中の全ての明示的な公開宣言を監査する。
方針：各工程で公開宣言の公理表示と型の検査を追加する。
規約：許される公理は propext・Classical.choice・Quot.sound のみ。
使われ方：対象ビルド後に `lake env lean scripts/audit_dg_nerve.lean` を実行する。
原典：HA Construction 1.3.1.6、Proposition 1.3.1.10。
単体的構造・ホーン充填の完成をこの監査から主張しない。
-/

#print axioms SerrePositivity.DifferentialGraded.differential_compose
#print axioms SerrePositivity.DifferentialGraded.compose_assoc
#print axioms SerrePositivity.DifferentialGraded.differential_unit
#print axioms SerrePositivity.DifferentialGraded.compose_unit
#print axioms SerrePositivity.DifferentialGraded.unit_compose

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
#print axioms SerrePositivity.InfinityCategories.DGNerve.two_eq_univ
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofEdge
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle_ofEdge
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge_edgeCycle
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeEquiv
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeClosed
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_id
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_comp
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_of_card_two
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_rhs_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_inj
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullbackOfInjective
#print axioms SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_card_two

-- 定義・主要定理の正確な型を同じ実行で確認する。
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
#check @SerrePositivity.InfinityCategories.DGNerve.two_eq_univ
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.ofEdge
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeCycle_ofEdge
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.ofEdge_edgeCycle
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeEquiv
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.edgeClosed
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.triangleHom
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.differential_triangleHom
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_hom_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_id
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_comp
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.rhs_of_card_two
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_term_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.SimplexData.pullback_rhs_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_inj
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullbackOfInjective
#check @SerrePositivity.InfinityCategories.DGNerve.Simplex.pullback_equation_of_card_two
