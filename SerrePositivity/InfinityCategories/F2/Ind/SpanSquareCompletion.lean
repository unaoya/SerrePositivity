module

public import SerrePositivity.InfinityCategories.F2.Ind.FilteredSquareCompletion
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpanSquareUniverseReading

/-!
概要：持ち上げた span 全余錐族の filtered 補完は、同じ実引き戻し性を保つ。
方針：正方形同型で全余錐を制限し、実四角形族の有限交換を適用する。
規約：元の全族と指定補完を固定し、有限交換は明示入力。
使われ方：Ind の同じ各段の cofiber 四角形から元の四角形への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ span 全余錐族の filtered 補完を、元の実引き戻し四角形へ戻す。 -/
lemma ind_spanSquare_completion_isPullback (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    {I C : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I] [Quasicategory C]
    (hex : CoherentFilteredLimitExchangeShape (horn 2 2 : SSet.{u}))
    (p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶
      (ihom (join ((SSet.uliftFunctor.{u + 1, u}).obj (horn 2 0))
        (Δ[0] : SSet.{u + 1}))).obj (IndInfinity κ C))
    (c : JoinCocone p)
    (hc : ∀ k, IsColimitCone (mapJoinCocone (indInclusionPresheaf κ C)
      (evaluateFunctorCocone c k)))
    (hp : ∀ i : I _⦋0⦌, IsPullbackSquare
      (((uliftSpanSquareReadingIso.{u, u + 1}).inv ≫
        (functorVertexCocone (p.app (Opposite.op ⦋0⦌) (ULift.up i))).val) ≫
          indInclusionPresheaf κ C)) :
    IsPullbackSquare ((uliftSpanSquareReadingIso.{u, u + 1}).inv ≫
      (functorVertexCocone c.vertex).val) := by
  let r := (uliftSpanSquareReadingIso.{u, u + 1}).inv
  have hr (i : I _⦋0⦌) : IsPullbackSquare
      (functorVertexSquare ((p ≫ (pre r).app (IndInfinity κ C)).app
        (Opposite.op ⦋0⦌) (ULift.up i)) ≫ indInclusionPresheaf κ C) := by
    change IsPullbackSquare ((functorVertexEquiv _ _).symm
      (((pre r).app (IndInfinity κ C)).app _ (p.app _ (ULift.up i))) ≫
        indInclusionPresheaf κ C)
    rw [functorVertexMap_precomp]
    exact hp i
  have ht := ind_filteredPullbackSquare_completion κ hκ hex
    (p ≫ (pre r).app (IndInfinity κ C)) (reindexFunctorCocone c r)
    (reindexFunctorCocone_image_isColimit c (indInclusionPresheaf κ C) hc r) hr
  change IsPullbackSquare ((functorVertexEquiv _ _).symm
    (((pre r).app (IndInfinity κ C)).app _ c.vertex)) at ht
  rw [functorVertexMap_precomp] at ht
  exact ht

end SerrePositivity.InfinityCategories.F2.Ind
