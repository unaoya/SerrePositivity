import SerrePositivity.InfinityCategories.DoldKanComparison
/-!
# Dold–Kan 比較の公理と型の監査

概要：γ1.5 の明示的な公開宣言の完全な型と依存公理を検査する。
方針：集約のビルド後に各宣言を #check @ と公理表示で確認する。
規約：許される公理は propext、Classical.choice、Quot.sound のみ。
使われ方：HA 1.3.1.13–1.3.1.17、Kerodon 2.5.7–2.5.9。γ1.5 全体は未完了。
-/

set_option pp.universes true
set_option pp.explicit true

#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.homModule
#check @SerrePositivity.InfinityCategories.DoldKanComparison.homModule
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.homSpace
#check @SerrePositivity.InfinityCategories.DoldKanComparison.homSpace
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.homSpaceLiftIso
#check @SerrePositivity.InfinityCategories.DoldKanComparison.homSpaceLiftIso
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.homSpaceLiftKan
#check @SerrePositivity.InfinityCategories.DoldKanComparison.homSpaceLiftKan
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.homSpaceKan
#check @SerrePositivity.InfinityCategories.DoldKanComparison.homSpaceKan
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.uliftSimplexHom
#check @SerrePositivity.InfinityCategories.DoldKanComparison.uliftSimplexHom
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.uliftSimplexHom_yonedaEquiv
#check @SerrePositivity.InfinityCategories.DoldKanComparison.uliftSimplexHom_yonedaEquiv
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.uliftSimplexHom_face
#check @SerrePositivity.InfinityCategories.DoldKanComparison.uliftSimplexHom_face
#print axioms SerrePositivity.InfinityCategories.DoldKanComparison.kanComplex_of_ulift
#check @SerrePositivity.InfinityCategories.DoldKanComparison.kanComplex_of_ulift
