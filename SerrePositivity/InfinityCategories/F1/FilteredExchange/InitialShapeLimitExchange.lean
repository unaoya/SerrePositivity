module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinCells
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ArrowColimitInvertibility
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FunctorVertexCone
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.InitialShapeConeCriterion

/-!
概要：始点で極限を検出できる形状では元の点ごとの余極限も極限錐を保つ。
方針：始点への元の脚の族を再添字付けし、指定余極限矢印の可逆性を使う。
規約：添字の filtered 性は不要。使われ方：有限セル帰納の単体条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 始点で検出できる形状の極限は、元の点ごとの余極限余錐で保存される。 -/
lemma pointwiseColimit_preserves_initialShapeLimits {J K X : SSet.{u}} [Quasicategory X]
    (a : (Δ[0] : SSet.{u}) ⟶ K) [Mono a] (ha : leftAnodyneExtensions a)
    {p : J ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj X} (c : JoinCocone p)
    (hc : IsPointwiseColimitCone c)
    (hp : ∀ j : J _⦋0⦌, IsLimitCone (functorVertexCone (p.app (Opposite.op ⦋0⦌) j))) :
    IsLimitCone (functorVertexCone c.vertex) := by
  let d := reindexFunctorCocone c (coneInitialLeg a)
  have hd : IsPointwiseColimitCone d := hc.reindex _
  have hi : ∀ j : J _⦋0⦌, IsEquivalencePathVertex
      ((p ≫ (pre (coneInitialLeg a)).app X).app (Opposite.op ⦋0⦌) j) := by
    intro j
    exact (isLimitCone_functorVertexCone_iff_initialLeg a ha
      (p.app (Opposite.op ⦋0⦌) j)).mp (hp j)
  have hv := isEquivalencePathVertex_of_pointwiseColimit d hd hi
  rw [reindexFunctorCocone_vertex] at hv
  exact (isLimitCone_functorVertexCone_iff_initialLeg a ha c.vertex).mpr hv

end SerrePositivity.InfinityCategories.F2
