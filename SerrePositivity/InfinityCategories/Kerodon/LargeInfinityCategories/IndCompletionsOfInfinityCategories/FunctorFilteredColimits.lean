module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaColimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.FunctorColimitConeExistence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeEvaluation

/-!
概要：Ind 関手圏で同じ小さい filtered 図式の点ごとの余極限を構成する。
方針：各値の Ind 余極限から全余錐を作り、包含による各値の保存を回収する。
規約：元の全図式と全余錐を保持し、形状の小ささや有限性を追加しない。
使われ方：単一 filtered 表示の全錐族を点ごとの余極限で補完する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 指定全図式は点ごとの filtered 余極限を持ち、その全評価を前層への包含が保存する。 -/
lemma exists_indFunctor_kappaFiltered_colimit (κ : Cardinal.{u})
    {I C : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I] [Quasicategory C]
    {K : SSet.{u + 1}}
    (p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c ∧
      ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c k)) := by
  obtain ⟨c, hc, hp⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.exists_colimitCone_functor_of_pointwise p
    (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasColimit κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram p k))
  have he (k : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c k) := hp k
  exact ⟨c, hc, he, fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_inclusion_isColimit κ _ _ (he k)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
