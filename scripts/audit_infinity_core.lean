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
