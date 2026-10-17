import SerrePositivity.InfinityCategories.Coherent
/-!
# Coherent nerve の公理監査

概要：γ1 の実装済みの明示的な公開宣言の公理と完全な型を表示する。
方針：全宣言を #print axioms と #check @ で個別に検査する。
規約：許される公理は propext、Classical.choice、Quot.sound のみ。
使われ方：対象と集約をビルド後、lake env lean scripts/audit_coherent_nerve.lean。
原典：HTT 1.1.5.10、Kerodon 2.4.3–2.4.5。γ1 全体は未完了。
-/

set_option pp.universes true
set_option pp.explicit true

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCylinder
#check @SerrePositivity.InfinityCategories.Coherent.hollowCylinder

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCylinder_anodyne
#check @SerrePositivity.InfinityCategories.Coherent.hollowCylinder_anodyne

#print axioms SerrePositivity.InfinityCategories.Coherent.hollowCylinder_extension
#check @SerrePositivity.InfinityCategories.Coherent.hollowCylinder_extension

#print axioms SerrePositivity.InfinityCategories.Coherent.path_hom_iff
#check @SerrePositivity.InfinityCategories.Coherent.path_hom_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathOfInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathOfInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInterior_pathOfInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathInterior_pathOfInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathOfInterior_pathInterior
#check @SerrePositivity.InfinityCategories.Coherent.pathOfInterior_pathInterior

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInteriorEquiv
#check @SerrePositivity.InfinityCategories.Coherent.pathInteriorEquiv

#print axioms SerrePositivity.InfinityCategories.Coherent.pathInterior_subset_iff
#check @SerrePositivity.InfinityCategories.Coherent.pathInterior_subset_iff

#print axioms SerrePositivity.InfinityCategories.Coherent.pathPrefix
#check @SerrePositivity.InfinityCategories.Coherent.pathPrefix

#print axioms SerrePositivity.InfinityCategories.Coherent.pathSuffix
#check @SerrePositivity.InfinityCategories.Coherent.pathSuffix

#print axioms SerrePositivity.InfinityCategories.Coherent.pathPrefix_comp_pathSuffix
#check @SerrePositivity.InfinityCategories.Coherent.pathPrefix_comp_pathSuffix

