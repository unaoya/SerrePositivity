module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.EraseEraseConfluence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MergeMergeConfluence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MergeEraseConfluence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReductionExistence

/-!
# 元の基本縮約の合流性と縮約済みの代表の一意性

概要：二つの基本縮約の全 fork が合流し、有限縮約の結果も合流する。
方針：三種類の局所合流を束ね、Church–Rosser と縮約済みの停止条件を適用する。
規約：元の語と全射列を含む対象の等式。余極限内の値の一致は仮定しない。
使われ方：元の有限縮約の一意な正規形。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) (n : SimplexCategoryᵒᵖ)

lemma reduction_local_join {r s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hs : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n r s) (ht : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n r t) :
    ∃ q, Relation.ReflGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) s q ∧
      Relation.ReflGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) t q := by
  cases hs with
  | merge d p hp τ =>
    cases ht with
    | merge d q hq τ => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.merge_merge_join W X Y d p q hp hq τ
    | erase j τ hj => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.merge_erase_join W X Y d p hp j τ hj
  | erase j τ hj =>
    cases ht with
    | merge d p hp τ =>
      obtain ⟨q, hq, hq'⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.merge_erase_join W X Y d p hp j τ hj
      exact ⟨q, hq', hq⟩
    | erase k τ hk => exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.erase_erase_join W X Y τ j k hj hk

lemma reduction_church_rosser {r s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hs : Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r s)
    (ht : Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r t) :
    Relation.Join (Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n)) s t := by
  apply Relation.church_rosser ?_ hs ht
  intro a b c hab hac
  obtain ⟨q, hbq, hcq⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reduction_local_join W X Y n hab hac
  exact ⟨q, hbq, hcq.to_reflTransGen⟩

lemma chain_eq_of_reduced {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y r)
    (h : Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r s) : r = s := by
  rcases h.cases_head with he | ⟨t, ht, _⟩
  · exact he
  · exact False.elim (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.no_reduction_of_reduced W X Y n hr ht)

lemma reduced_representative_unique {r s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hs : Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r s)
    (ht : Relation.ReflTransGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n) r t)
    (hsr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y s) (htr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y t) : s = t := by
  obtain ⟨q, hsq, htq⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reduction_church_rosser W X Y n hs ht
  exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.chain_eq_of_reduced W X Y n hsr hsq).trans
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.chain_eq_of_reduced W X Y n htr htq).symm

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
