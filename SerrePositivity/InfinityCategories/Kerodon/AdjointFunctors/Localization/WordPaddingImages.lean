module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPadding

/-!
# 両端の語を固定した列追加による像の交わりの保存

概要：両端を固定した元の列追加関手は、元の列の像の交わりを保つ。
方針：左端・中央・右端の列に分け、連結写像の像の特徴付けを使う。
規約：両端の全列を共有する同じ元の関手の写像を比較する。
使われ方：padding で前合成した図式の proper 性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma sandwichMap_intersection_range (p q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c) :
    Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichFunctor p q).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g)).orderHom =
      Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichFunctor p q).map f).orderHom ∩
        Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sandwichFunctor p q).map g).orderHom := by
  change Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (𝟙 p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion f g) (𝟙 q))).orderHom =
    Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (𝟙 p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap f (𝟙 q))).orderHom ∩
      Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap (𝟙 p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.appendMap g (𝟙 q))).orderHom
  ext j
  cases j using Fin.addCases with
  | left j =>
    simp only [Set.mem_inter_iff]
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left]
    exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | right j =>
    simp only [Set.mem_inter_iff]
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right]
    cases j using Fin.addCases with
    | left j =>
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_left]
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intersectionInclusion_range]
      rfl
    | right j =>
      erw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.appendMap_range_right]
      exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (sandwichMap_intersection_range)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
