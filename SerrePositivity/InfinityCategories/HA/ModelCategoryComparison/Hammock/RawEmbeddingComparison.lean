module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.GraphEmbedding

/-!
# 同じ元の像を持つ未縮約 hammock の比較

概要：同じ列の像を持つ二つの包含が同じ全射列を与えるなら、元の未縮約対象は等しい。
方針：語の包含の一意性と graph の単射性で元の語と全射列を回収する。
規約：余極限内の値の一致だけからは比較を推論しない。
使われ方：異なる順序の削除の共通の縮約対象の同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

lemma raw_eq_of_embeddings {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    [W.IsMultiplicative] (X Y : C) {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (hfg : Set.range f.orderHom = Set.range g.orderHom) (n : SimplexCategoryᵒᵖ)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X Y).obj n)
    (hστ : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n σ = ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map g).app n τ) :
    (⟨a, σ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) = ⟨b, τ⟩ := by
  obtain ⟨hab, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embedding_eq_of_range f g hf hg hfg
  cases hab
  rw [eqToHom_refl, Category.id_comp] at he
  subst f
  have hh : σ = τ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphDiagram_map_app_injective W g hg X Y n hστ
  cases hh
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
