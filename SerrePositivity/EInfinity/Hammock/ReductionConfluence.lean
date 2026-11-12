module

public import SerrePositivity.EInfinity.Hammock.EraseEraseConfluence
public import SerrePositivity.EInfinity.Hammock.MergeMergeConfluence
public import SerrePositivity.EInfinity.Hammock.MergeEraseConfluence
public import SerrePositivity.EInfinity.Hammock.ReductionExistence

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

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) (n : SimplexCategoryᵒᵖ)

lemma reduction_local_join {r s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hs : Reduction W X Y n r s) (ht : Reduction W X Y n r t) :
    ∃ q, Relation.ReflGen (Reduction W X Y n) s q ∧
      Relation.ReflGen (Reduction W X Y n) t q := by
  cases hs with
  | merge d p hp τ =>
    cases ht with
    | merge d q hq τ => exact merge_merge_join W X Y d p q hp hq τ
    | erase j τ hj => exact merge_erase_join W X Y d p hp j τ hj
  | erase j τ hj =>
    cases ht with
    | merge d p hp τ =>
      obtain ⟨q, hq, hq'⟩ := merge_erase_join W X Y d p hp j τ hj
      exact ⟨q, hq', hq⟩
    | erase k τ hk => exact erase_erase_join W X Y τ j k hj hk

lemma reduction_church_rosser {r s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hs : Relation.ReflTransGen (Reduction W X Y n) r s)
    (ht : Relation.ReflTransGen (Reduction W X Y n) r t) :
    Relation.Join (Relation.ReflTransGen (Reduction W X Y n)) s t := by
  apply Relation.church_rosser ?_ hs ht
  intro a b c hab hac
  obtain ⟨q, hbq, hcq⟩ := reduction_local_join W X Y n hab hac
  exact ⟨q, hbq, hcq.to_reflTransGen⟩

lemma chain_eq_of_reduced {r s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y r)
    (h : Relation.ReflTransGen (Reduction W X Y n) r s) : r = s := by
  rcases h.cases_head with he | ⟨t, ht, _⟩
  · exact he
  · exact False.elim (no_reduction_of_reduced W X Y n hr ht)

lemma reduced_representative_unique {r s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n}
    (hs : Relation.ReflTransGen (Reduction W X Y n) r s)
    (ht : Relation.ReflTransGen (Reduction W X Y n) r t)
    (hsr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y s) (htr : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock.IsReduced W X Y t) : s = t := by
  obtain ⟨q, hsq, htq⟩ := reduction_church_rosser W X Y n hs ht
  exact (chain_eq_of_reduced W X Y n hsr hsq).trans
    (chain_eq_of_reduced W X Y n htr htq).symm

end SerrePositivity.EInfinity.Hammock
