module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FilteredLimitConeCompletion
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SquareFamilyReading
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeReindexImage

/-!
概要：同じ全四角形族の点ごとの filtered 補完は普遍四角形を保つ。
方針：引き戻し錐には明示の有限交換、押し出し余錐には余極限同士の交換を適用する。
規約：元の全族・元の補完余錐・その同じ頂点の実四角形を固定する。
使われ方：I-2 c の段ごとの bicartesian 四角形から Ind の元の四角形への接続。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 点ごとの filtered 補完は、包含が保存する元の引き戻し全四角形族を引き戻しへ送る。 -/
lemma ind_filteredPullbackSquare_completion (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {I C : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I] [Quasicategory C]
    (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredLimitExchangeShape (horn 2 2 : SSet.{u}))
    (p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c k)))
    (hp : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare (p.app (Opposite.op ⦋0⦌) (ULift.up i)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare c.vertex) := by
  let r := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftCospanSquareReading.{u, u + 1}
  let q := p ≫ (pre r).app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  let d := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reindexFunctorCocone c r
  have hr (i : I _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (q.app (Opposite.op ⦋0⦌) (ULift.up i)))) := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone_postcompose_isLimit_iff _ _).mp
    apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare_pullback_iff.{u, u + 1}
      (((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C)).app (Opposite.op ⦋0⦌)
          (p.app (Opposite.op ⦋0⦌) (ULift.up i)))).mpr
    rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare_postcompose]
    exact hp i
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_filteredLimitCone_isLimit κ hκ hex q d
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reindexFunctorCocone_image_isColimit c (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) hc r) hr
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare_pullback_iff c.vertex).mp ht.1

/-- 点ごとの余極限補完は、同じ元の押し出し全四角形族を押し出しへ送る。 -/
lemma ind_pushoutSquare_completion (κ : Cardinal.{u})
    {I : SSet.{u + 1}} {C : SSet.{u}} [Quasicategory C]
    (p : I ⟶ (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c)
    (hp : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare (p.app (Opposite.op ⦋0⦌) i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare c.vertex) := by
  let r := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.{u + 1}).hom
  let q := p ≫ (pre r).app (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  let d := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.reindexFunctorCocone c r
  have hr (i : I _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.functorVertexCocone (q.app (Opposite.op ⦋0⦌) i)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare_pushout_iff _).mpr (hp i)
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeFamily_completion_isColimit q d (hc.reindex r) hr
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexSquare_pushout_iff c.vertex).mp ht

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
