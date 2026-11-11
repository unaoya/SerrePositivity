module

public import SerrePositivity.EInfinity.Hammock.UnmarkedValueNonempty
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorWordPathFlatten

/-!
# 元の全列の順序付き文字列としての hammock の値

概要：元の評価は元の全列の非指定文字列を順序通り連結したものである。
方針：既存の値の射列の全合成と各隣接列の回収式を使う。
規約：空語と元の端点表示を含む。
使われ方：切断した prefix・生成矢・残りの値の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C}

lemma value_flatten (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y) :
    value W S = (List.ofFn (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S)).flatten := by
  rw [value_path_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composable_hom_flatten]
  congr 2
  funext i
  exact path_adjacent_column W S i

lemma value_eq_nil_of_marked (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths w X Y)
    (h : ∀ i, W.paths (S.arrow i)) : value W S = [] :=
  (value_eq_nil_iff W S).2 fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W (S.arrow i) (h i)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
