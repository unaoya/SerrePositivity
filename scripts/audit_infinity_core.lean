import SerrePositivity.InfinityCategories.Core

/-!
概要：Core の明示的な公開宣言の型と公理を監査する。
方針：各工程で全宣言について `#check` と `#print axioms` を追加する。
規約：許す公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
使われ方：HTT §1.2.3、Kerodon §1.4.5 の実装を対象ビルド後に検査する。
-/

#check @SerrePositivity.InfinityCategories.pathToEdgeHomotopyCategory
#check @SerrePositivity.InfinityCategories.homotopic_path_eq
#check @SerrePositivity.InfinityCategories.edgeToPathHomotopyCategory
#check @SerrePositivity.InfinityCategories.edge_path_inverse
#check @SerrePositivity.InfinityCategories.path_edge_inverse
#check @SerrePositivity.InfinityCategories.homotopyCategoryBridge

#print axioms SerrePositivity.InfinityCategories.pathToEdgeHomotopyCategory
#print axioms SerrePositivity.InfinityCategories.homotopic_path_eq
#print axioms SerrePositivity.InfinityCategories.edgeToPathHomotopyCategory
#print axioms SerrePositivity.InfinityCategories.edge_path_inverse
#print axioms SerrePositivity.InfinityCategories.path_edge_inverse
#print axioms SerrePositivity.InfinityCategories.homotopyCategoryBridge

#check @SerrePositivity.InfinityCategories.HomotopyCategoryMap.map
#check @SerrePositivity.InfinityCategories.HomotopyCategoryMap.map_id
#check @SerrePositivity.InfinityCategories.HomotopyCategoryMap.map_comp
#check @SerrePositivity.InfinityCategories.HomotopyCategoryMap.bridge_naturality
#print axioms SerrePositivity.InfinityCategories.HomotopyCategoryMap.map
#print axioms SerrePositivity.InfinityCategories.HomotopyCategoryMap.map_id
#print axioms SerrePositivity.InfinityCategories.HomotopyCategoryMap.map_comp
#print axioms SerrePositivity.InfinityCategories.HomotopyCategoryMap.bridge_naturality

#check @SerrePositivity.InfinityCategories.homotopyIntervalEdge
#check @SerrePositivity.InfinityCategories.homotopyNatTrans
#check @SerrePositivity.InfinityCategories.homotopyNatTrans_app
#check @SerrePositivity.InfinityCategories.homotopyNatTransOfEndpoints
#print axioms SerrePositivity.InfinityCategories.homotopyIntervalEdge
#print axioms SerrePositivity.InfinityCategories.homotopyNatTrans
#print axioms SerrePositivity.InfinityCategories.homotopyNatTrans_app
#print axioms SerrePositivity.InfinityCategories.homotopyNatTransOfEndpoints

#check @SerrePositivity.InfinityCategories.nerveHomotopyCategoryEquivalence
#check @SerrePositivity.InfinityCategories.nerveBridge_map_edge
#print axioms SerrePositivity.InfinityCategories.nerveHomotopyCategoryEquivalence
#print axioms SerrePositivity.InfinityCategories.nerveBridge_map_edge

-- A2a の前段階：join 自体の関手法則・包含・同型の完成は未主張。
#check @SerrePositivity.InfinityCategories.Join.augObj
#check @SerrePositivity.InfinityCategories.Join.augMap
#check @SerrePositivity.InfinityCategories.Join.augMap_id
#check @SerrePositivity.InfinityCategories.Join.augMap_comp
#check @SerrePositivity.InfinityCategories.Join.Simplex
#check @SerrePositivity.InfinityCategories.Join.pullCut
#check @SerrePositivity.InfinityCategories.Join.pullCut_le
#check @SerrePositivity.InfinityCategories.Join.lt_pullCut_iff
#check @SerrePositivity.InfinityCategories.Join.cut_ext
#check @SerrePositivity.InfinityCategories.Join.pullCut_id
#check @SerrePositivity.InfinityCategories.Join.pullCut_comp
#check @SerrePositivity.InfinityCategories.Join.leftMap
#check @SerrePositivity.InfinityCategories.Join.rightMap
#check @SerrePositivity.InfinityCategories.Join.simplexMap
#print axioms SerrePositivity.InfinityCategories.Join.augObj
#print axioms SerrePositivity.InfinityCategories.Join.augMap
#print axioms SerrePositivity.InfinityCategories.Join.augMap_id
#print axioms SerrePositivity.InfinityCategories.Join.augMap_comp
#print axioms SerrePositivity.InfinityCategories.Join.Simplex
#print axioms SerrePositivity.InfinityCategories.Join.pullCut
#print axioms SerrePositivity.InfinityCategories.Join.pullCut_le
#print axioms SerrePositivity.InfinityCategories.Join.lt_pullCut_iff
#print axioms SerrePositivity.InfinityCategories.Join.cut_ext
#print axioms SerrePositivity.InfinityCategories.Join.pullCut_id
#print axioms SerrePositivity.InfinityCategories.Join.pullCut_comp
#print axioms SerrePositivity.InfinityCategories.Join.leftMap
#print axioms SerrePositivity.InfinityCategories.Join.rightMap
#print axioms SerrePositivity.InfinityCategories.Join.simplexMap

-- A2a 途中：直接構成の関手法則・包含・部分複体・空 join。
#check @SerrePositivity.InfinityCategories.Join.augHom
#check @SerrePositivity.InfinityCategories.Join.augHom_naturality
#check @SerrePositivity.InfinityCategories.Join.augHom_id
#check @SerrePositivity.InfinityCategories.Join.augHom_comp
#check @SerrePositivity.InfinityCategories.Join.augHom_injective
#check @SerrePositivity.InfinityCategories.Join.stdAugEquiv
#check @SerrePositivity.InfinityCategories.Join.concat
#check @SerrePositivity.InfinityCategories.Join.concat_lt_iff
#check @SerrePositivity.InfinityCategories.Join.Simplex.ext
#check @SerrePositivity.InfinityCategories.Join.augMap_congr
#check @SerrePositivity.InfinityCategories.Join.pullCut_zero
#check @SerrePositivity.InfinityCategories.Join.pullCut_all
#check @SerrePositivity.InfinityCategories.Join.pullCut_concat
#check @SerrePositivity.InfinityCategories.Join.simplexMap_id
#check @SerrePositivity.InfinityCategories.Join.simplexMap_comp
#check @SerrePositivity.InfinityCategories.Join.Simplex.inl
#check @SerrePositivity.InfinityCategories.Join.Simplex.inr
#check @SerrePositivity.InfinityCategories.Join.simplexMap_inl
#check @SerrePositivity.InfinityCategories.Join.simplexMap_inr
#check @SerrePositivity.InfinityCategories.join
#check @SerrePositivity.InfinityCategories.joinMap
#check @SerrePositivity.InfinityCategories.joinMap_id
#check @SerrePositivity.InfinityCategories.joinMap_comp
#check @SerrePositivity.InfinityCategories.joinMap_mono
#check @SerrePositivity.InfinityCategories.joinInl
#check @SerrePositivity.InfinityCategories.joinInr
#check @SerrePositivity.InfinityCategories.joinInl_joinMap
#check @SerrePositivity.InfinityCategories.joinInr_joinMap
#check @SerrePositivity.InfinityCategories.joinSubcomplexLeft
#check @SerrePositivity.InfinityCategories.joinSubcomplexRight
#check @SerrePositivity.InfinityCategories.joinUnion
#check @SerrePositivity.InfinityCategories.joinSubcomplexLeftIso
#check @SerrePositivity.InfinityCategories.joinSubcomplexRightIso
#check @SerrePositivity.InfinityCategories.joinSubcomplexLeftIso_hom_ι
#check @SerrePositivity.InfinityCategories.joinSubcomplexRightIso_hom_ι
#check @SerrePositivity.InfinityCategories.emptyJoinIso
#check @SerrePositivity.InfinityCategories.joinInl_joinMap_assoc
#check @SerrePositivity.InfinityCategories.joinInr_joinMap_assoc
#print axioms SerrePositivity.InfinityCategories.Join.augHom
#print axioms SerrePositivity.InfinityCategories.Join.augHom_naturality
#print axioms SerrePositivity.InfinityCategories.Join.augHom_id
#print axioms SerrePositivity.InfinityCategories.Join.augHom_comp
#print axioms SerrePositivity.InfinityCategories.Join.augHom_injective
#print axioms SerrePositivity.InfinityCategories.Join.stdAugEquiv
#print axioms SerrePositivity.InfinityCategories.Join.concat
#print axioms SerrePositivity.InfinityCategories.Join.concat_lt_iff
#print axioms SerrePositivity.InfinityCategories.Join.Simplex.ext
#print axioms SerrePositivity.InfinityCategories.Join.augMap_congr
#print axioms SerrePositivity.InfinityCategories.Join.pullCut_zero
#print axioms SerrePositivity.InfinityCategories.Join.pullCut_all
#print axioms SerrePositivity.InfinityCategories.Join.pullCut_concat
#print axioms SerrePositivity.InfinityCategories.Join.simplexMap_id
#print axioms SerrePositivity.InfinityCategories.Join.simplexMap_comp
#print axioms SerrePositivity.InfinityCategories.Join.Simplex.inl
#print axioms SerrePositivity.InfinityCategories.Join.Simplex.inr
#print axioms SerrePositivity.InfinityCategories.Join.simplexMap_inl
#print axioms SerrePositivity.InfinityCategories.Join.simplexMap_inr
#print axioms SerrePositivity.InfinityCategories.join
#print axioms SerrePositivity.InfinityCategories.joinMap
#print axioms SerrePositivity.InfinityCategories.joinMap_id
#print axioms SerrePositivity.InfinityCategories.joinMap_comp
#print axioms SerrePositivity.InfinityCategories.joinMap_mono
#print axioms SerrePositivity.InfinityCategories.joinInl
#print axioms SerrePositivity.InfinityCategories.joinInr
#print axioms SerrePositivity.InfinityCategories.joinInl_joinMap
#print axioms SerrePositivity.InfinityCategories.joinInr_joinMap
#print axioms SerrePositivity.InfinityCategories.joinSubcomplexLeft
#print axioms SerrePositivity.InfinityCategories.joinSubcomplexRight
#print axioms SerrePositivity.InfinityCategories.joinUnion
#print axioms SerrePositivity.InfinityCategories.joinSubcomplexLeftIso
#print axioms SerrePositivity.InfinityCategories.joinSubcomplexRightIso
#print axioms SerrePositivity.InfinityCategories.joinSubcomplexLeftIso_hom_ι
#print axioms SerrePositivity.InfinityCategories.joinSubcomplexRightIso_hom_ι
#print axioms SerrePositivity.InfinityCategories.emptyJoinIso
#print axioms SerrePositivity.InfinityCategories.joinInl_joinMap_assoc
#print axioms SerrePositivity.InfinityCategories.joinInr_joinMap_assoc
