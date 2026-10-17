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
