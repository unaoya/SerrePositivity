module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIntersection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordFactorization
public import Mathlib.Data.Fintype.Card

/-!
# 元の語の写像の列の像を経由する因子分解

概要：任意の元の語の写像を、短い像への全射と元の包含に厳密に分ける。
方針：列の像の部分語への持ち上げと、元の包含の単射性を使う。
規約：像の語の長さは始域以下。元の列の順序と色を保持する。
使われ方：前段階から最大長の交互方向語への射の境界を経由する分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)

def imageWord : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subword b (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (imageWord)


def imageInclusion : imageWord f ⟶ b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion b (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (imageInclusion)


lemma imageInclusion_injective : Function.Injective (imageInclusion f).orderHom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_injective _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (imageInclusion_injective)


lemma imageInclusion_range : Set.range (imageInclusion f).orderHom = Set.range f.orderHom := by
  change Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion b (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnImage f)).orderHom = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subwordInclusion_range, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coe_columnImage]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (imageInclusion_range)


def toImage : a ⟶ imageWord f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding (imageInclusion f) (imageInclusion_injective f) f (by
    rw [imageInclusion_range])).val

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (toImage)


lemma toImage_fac : toImage f ≫ imageInclusion f = f :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.factorEmbedding (imageInclusion f) (imageInclusion_injective f) f (by
    rw [imageInclusion_range])).property

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (toImage_fac)


lemma toImage_surjective : Function.Surjective (toImage f).orderHom := by
  intro j
  have hm : (imageInclusion f).orderHom j ∈ Set.range f.orderHom := by
    rw [← imageInclusion_range f]
    exact ⟨j, rfl⟩
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, imageInclusion_injective f ?_⟩
  have he := congrArg (fun h : a ⟶ b => h.orderHom i) (toImage_fac f)
  exact he.trans hi

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (toImage_surjective)


lemma imageWord_length_le : (imageWord f).length ≤ a.length := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective _ (toImage_surjective f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (imageWord_length_le)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
