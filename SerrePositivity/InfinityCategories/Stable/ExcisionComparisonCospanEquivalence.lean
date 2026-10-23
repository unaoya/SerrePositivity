module
public import SerrePositivity.InfinityCategories.Stable.ExcisionRawParameterRestriction
public import SerrePositivity.InfinityCategories.Stable.ExcisionPullbackComparisonFamily
public import SerrePositivity.InfinityCategories.Stable.FunctorEdgeArrowReadback
public import SerrePositivity.InfinityCategories.Stable.PullbackComparisonComponentInvertible

/-!
概要：四つの実 suspension 面の引き戻し性から、元の押し出しの像の普遍性を導く。
方針：全 cospan の厳密保存、同じ θ と対角合成、元の入力面の極限錐を接続する。
規約：標的の零対象や一般安定性は仮定しない。使われ方：一般切除・loop 同値判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma excisionComparison_cospan_isEquivalencePath {X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] {F : nerve ExcisionGridIndex.{u} ⟶ X}
    (c : JoinCone (nerveMap (posetSubtypeInclusion IsExcisionFullPunctured) ≫ F))
    (d : JoinCone (pullbackCospan (excisionRawSuspensionSquare (excisionReplaceInitial c))))
    (hd : IsLimitCone d)
    (hF : ∀ k : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌,
      IsPullbackSquare (excisionRawSuspensionSquare F ≫ evaluateFunctorAt k))
    (j : (horn 2 2 : SSet.{u}) _⦋0⦌) :
    IsEquivalencePathVertex ((pullbackCospan (excisionPullbackComparisonFamily c d hd)).app
      (Opposite.op ⦋0⦌) j) := by
  let k := cospanSquareBoundary.app (Opposite.op ⦋0⦌) j
  have hQ : IsPullbackSquare
      (excisionRawSuspensionSquare (excisionReplaceInitial c) ≫ evaluateFunctorAt k) := by
    rw [excisionRawSuspensionSquare_replaced_evaluate_cospan c j]
    exact hF k
  have he := functorPullbackComparison_component_isInvertible
    (excisionRawSuspensionSquare (excisionReplaceInitial c)) d hd k hQ
  have h := arrowFamilyOfFunctorEdge_vertex_edge
    (functorPullbackComparisonEdge (excisionRawSuspensionSquare (excisionReplaceInitial c))
      d hd) k
  exact (isInvertibleEdge_congr h).mpr he

end SerrePositivity.InfinityCategories
