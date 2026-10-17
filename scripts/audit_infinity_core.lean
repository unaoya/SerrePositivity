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
