module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordImageFactorization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmbeddingUniqueness

/-!
# 元の列部分集合の包含と単射の像の表示

概要：元の列部分集合の包含はその集合を像とし、任意の単射の像の語と厳密に比較できる。
方針：有限列の像の等式と元の包含の一意性を使う。
規約：部分集合の card と元の語の長さを保持する。
使われ方：境界の有限和表示と proper の交わりの適用。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma columnImage_subwordInclusion (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (s : Finset (Fin c.length)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion c s) = s := by
  apply Finset.coe_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coe_columnImage, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_range]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (columnImage_subwordInclusion)


lemma embedding_image_eq {a c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c) (hf : Function.Injective f.orderHom) :
    ∃ h : a = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageWord f, eqToHom h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion f = f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.embedding_eq_of_range f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion f) hf (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion_injective f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.imageInclusion_range f).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (embedding_image_eq)


lemma columnImage_card_of_injective {a c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ c)
    (hf : Function.Injective f.orderHom) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage f).card = a.length := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (columnImage_card_of_injective)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
