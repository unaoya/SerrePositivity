module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordErasure
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ProperDiagram

/-!
# 元の全単体から恒等列を一つ削除する操作

概要：全行が恒等列である一列を削除し、同じ元の全射列の原像を回収する。
方針：完成済みの像の特徴付けと単射性を使う。
規約：削除対象を同型類だけで指定せず、元の包含後の厳密な一致を証明する。
使われ方：縮約 hammock の基本削除と元の余極限への整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length) {n : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n) (hτ : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj k) j)
include hτ

lemma exists_eraseSimplex : ∃ σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j) X Y).obj n,
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j)).app n σ = τ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff_identityOutside (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective w j) n τ).2
      (fun k => (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityOutside_erase_iff (τ.obj k) j).2 (hτ k))

/-- 全行が恒等である元の一列を削除した、同じ全射列の原像。 -/
def eraseSimplex : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j) X Y).obj n :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exists_eraseSimplex W X Y j τ hτ)

lemma eraseSimplex_fac :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j)).app n
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ) = τ :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.exists_eraseSimplex W X Y j τ hτ)

lemma eraseSimplex_unique (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j) X Y).obj n)
    (hσ : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j)).app n σ = τ) :
    σ = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ := by
  apply _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphDiagram_map_app_injective W _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective w j) X Y n
  exact hσ.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex_fac W X Y j τ hτ).symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
