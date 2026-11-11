module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FiniteColimitFromPresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FinitePosetDiagramPresentation

/-!
概要：元の有限半順序全図式の Ind 内での余極限存在。
方針：元の同じ全図式の単一 filtered 表示と全余極限族の補完を使う。
規約：Yoneda の有限余極限保存に必要な交換入力を明示する。
使われ方：Ind の押し出しと安定性への接続。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 明示交換入力のもとで、元の有限半順序全図式は Ind 内に余極限を持つ。 -/
lemma indFinitePoset_hasColimit (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    {P : Type u} [PartialOrder P] [Finite P] {C : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasColimit_of_singleFilteredDiagramPresentation κ hκ hex D
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indFinitePoset_has_singleFilteredDiagramPresentation κ D)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
