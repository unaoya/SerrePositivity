module

public import SerrePositivity.EInfinity.Hammock.ReductionConfluence
public import SerrePositivity.EInfinity.Hammock.ReductionNaturality

/-!
# 元の有限縮約の一意な正規形

概要：任意の未縮約対象に、元の基本縮約で到達する一意な縮約済みの代表を選ぶ。
方針：有限到達と合流性による一意性を使い、選択に依存しない法則を得る。
規約：任意の語の遷移に対する不変性は別途必要。値の一致からは推論しない。
使われ方：縮約済みの単体集合の全作用素。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) (n : SimplexCategoryᵒᵖ)

/-- 元の有限縮約で得る縮約済みの代表。一意性により選択には依存しない。 -/
def normalForm (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n :=
  Classical.choose (exists_reduced_representative W X Y n r)

lemma normalForm_chain (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    Relation.ReflTransGen (Reduction W X Y n) r (normalForm W X Y n r) :=
  (Classical.choose_spec (exists_reduced_representative W X Y n r)).1

lemma normalForm_reduced (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y (normalForm W X Y n r) :=
  (Classical.choose_spec (exists_reduced_representative W X Y n r)).2

lemma normalForm_eq_of_chain {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (h : Relation.ReflTransGen (Reduction W X Y n) r s) :
    normalForm W X Y n r = normalForm W X Y n s :=
  reduced_representative_unique W X Y n (normalForm_chain W X Y n r)
    (h.trans (normalForm_chain W X Y n s))
    (normalForm_reduced W X Y n r) (normalForm_reduced W X Y n s)

lemma normalForm_eq_of_reduction {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (h : Reduction W X Y n r s) : normalForm W X Y n r = normalForm W X Y n s :=
  normalForm_eq_of_chain W X Y n (Relation.ReflTransGen.single h)

lemma normalForm_eq_self {r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n} (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y r) :
    normalForm W X Y n r = r :=
  (chain_eq_of_reduced W X Y n hr (normalForm_chain W X Y n r)).symm

lemma normalForm_idempotent (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    normalForm W X Y n (normalForm W X Y n r) = normalForm W X Y n r :=
  normalForm_eq_self W X Y n (normalForm_reduced W X Y n r)

lemma normalForm_value (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y (normalForm W X Y n r) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.value W X Y r :=
  (Reduction.chain_value_eq (normalForm_chain W X Y n r)).symm

lemma normalForm_eq_iff_join (r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    normalForm W X Y n r = normalForm W X Y n s ↔
      Relation.Join (Relation.ReflTransGen (Reduction W X Y n)) r s := by
  constructor
  · intro h
    refine ⟨normalForm W X Y n r, normalForm_chain W X Y n r, ?_⟩
    rw [h]
    exact normalForm_chain W X Y n s
  · rintro ⟨q, hrq, hsq⟩
    exact (normalForm_eq_of_chain W X Y n hrq).trans (normalForm_eq_of_chain W X Y n hsq).symm

lemma normalForm_map_normalForm {m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n) :
    normalForm W X Y m (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map W X Y α (normalForm W X Y n r)) =
      normalForm W X Y m (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.map W X Y α r) :=
  (normalForm_eq_of_chain W X Y m
    (Reduction.chain_map (normalForm_chain W X Y n r) α)).symm

end SerrePositivity.EInfinity.Hammock
