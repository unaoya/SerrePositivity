module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordEmbeddingUniqueness
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RawHammock
public import SerrePositivity.EInfinity.Hammock.GraphEmbedding

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

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

lemma raw_eq_of_embeddings {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    [W.IsMultiplicative] (X Y : C) {a b c : Word} (f : a ⟶ c) (g : b ⟶ c)
    (hf : Function.Injective f.orderHom) (hg : Function.Injective g.orderHom)
    (hfg : Set.range f.orderHom = Set.range g.orderHom) (n : SimplexCategoryᵒᵖ)
    (σ : (graph W a X Y).obj n) (τ : (graph W b X Y).obj n)
    (hστ : ((graphDiagram W X Y).map f).app n σ = ((graphDiagram W X Y).map g).app n τ) :
    (⟨a, σ⟩ : RawHammock W X Y n) = ⟨b, τ⟩ := by
  obtain ⟨hab, he⟩ := Word.embedding_eq_of_range f g hf hg hfg
  cases hab
  rw [eqToHom_refl, Category.id_comp] at he
  subst f
  have hh : σ = τ := graphDiagram_map_app_injective W g hg X Y n hστ
  cases hh
  rfl

end SerrePositivity.EInfinity.Hammock
