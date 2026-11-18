module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RawEmbeddingComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction

/-!
# 一列を除いた任意の包含による元の基本削除

概要：像が一列の補集合である元の包含は、既存の一列削除と同じ未縮約対象を与える。
方針：像の特徴付けで全射列を持ち上げ、元の包含の単射性で比較する。
規約：語を含む元の raw の等式を用い、余極限内の値で代用しない。
使われ方：混合縮約の可換四角形と明示的な単体圏の削除。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom)
  (j : Fin b.length) (hRange : Set.range f.orderHom = {j}ᶜ) {n : SimplexCategoryᵒᵖ}

include hRange

omit [W.IsMultiplicative] in
lemma identityOutside_of_complement (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn S j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityOutside f S := by
  intro l hl
  have hlj : l = j := by
    by_contra h
    have hm : l ∈ Set.range f.orderHom := by rw [hRange]; exact h
    obtain ⟨i, hi⟩ := hm
    exact hl i hi
  simpa only [hlj] using hj

include hf

lemma erase_raw_eq_of_embedding (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X Y).obj n) (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j)
    (hfac : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n σ = τ) :
    (⟨a, σ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) = ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase b j, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ⟩ :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.raw_eq_of_embeddings W X Y f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion b j) hf
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective b j) (hRange.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range b j).symm)
    n σ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ) (hfac.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex_fac W X Y j τ hτ).symm)

lemma exists_eraseEmbedding (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X Y).obj n)
    (hτ : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j) :
    ∃ σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n,
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n σ = τ ∧
      (⟨a, σ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) = ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase b j, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ⟩ := by
  obtain ⟨σ, hσ⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff_identityOutside f hf n τ).2
    (fun r => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.identityOutside_of_complement W X Y f j hRange (τ.obj r) (hτ r))
  exact ⟨σ, hσ, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.erase_raw_eq_of_embedding W X Y f hf j hRange σ τ hτ hσ⟩

lemma erase_reduction_of_embedding (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n)
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b X Y).obj n) (hfac : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n σ = τ) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n ⟨b, τ⟩ ⟨a, σ⟩ := by
  have ho := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagram_map_range_iff_identityOutside f hf n τ).1 ⟨σ, hfac⟩
  have hj : ∀ r, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj r) j := by
    intro r
    apply ho r j
    intro i hi
    have hm : j ∈ Set.range f.orderHom := ⟨i, hi⟩
    rw [hRange] at hm
    exact hm rfl
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.erase_raw_eq_of_embedding W X Y f hf j hRange σ τ hj hfac]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.erase j τ hj

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
