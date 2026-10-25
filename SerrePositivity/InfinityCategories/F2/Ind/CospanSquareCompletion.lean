module

public import SerrePositivity.InfinityCategories.F2.Ind.FilteredSquareCompletion

/-!
概要：持ち上げた cospan 全錐族の点ごとの補完は、同じ実押し出し性を保つ。
方針：元の正方形同型で全余錐を制限し、実四角形族の余極限補完を適用する。
規約：元の全錐族・指定補完余錐とその同じ頂点を保持する。
使われ方：Ind の単一表示から作った極限全錐の bicartesian 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の cospan 全錐族の同じ点ごとの補完を、実押し出し四角形へ戻す。 -/
lemma ind_cospanSquare_completion_isPushout (κ : Cardinal.{u})
    {I : SSet.{u + 1}} {C : SSet.{u}} [Quasicategory C]
    (p : I ⟶ (ihom (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (horn 2 2)))).obj (IndInfinity κ C))
    (c : JoinCocone p) (hc : IsPointwiseColimitCone c)
    (hp : ∀ i, IsPushoutSquare ((uliftCospanSquareReadingIso.{u, u + 1}).inv ≫
      (functorVertexCone (p.app (Opposite.op ⦋0⦌) i)).val)) :
    IsPushoutSquare ((uliftCospanSquareReadingIso.{u, u + 1}).inv ≫
      (functorVertexCone c.vertex).val) := by
  let r := (uliftCospanSquareReadingIso.{u, u + 1}).inv
  have hr (i : I _⦋0⦌) : IsPushoutSquare
      (functorVertexSquare ((p ≫ (pre r).app (IndInfinity κ C)).app
        (Opposite.op ⦋0⦌) i)) := by
    change IsPushoutSquare ((functorVertexEquiv _ _).symm
      (((pre r).app (IndInfinity κ C)).app _ (p.app _ i)))
    rw [functorVertexMap_precomp]
    exact hp i
  have ht := ind_pushoutSquare_completion κ (p ≫ (pre r).app (IndInfinity κ C))
    (reindexFunctorCocone c r) (hc.reindex r) hr
  change IsPushoutSquare ((functorVertexEquiv _ _).symm
    (((pre r).app (IndInfinity κ C)).app _ c.vertex)) at ht
  rw [functorVertexMap_precomp] at ht
  exact ht

end SerrePositivity.InfinityCategories.F2.Ind
