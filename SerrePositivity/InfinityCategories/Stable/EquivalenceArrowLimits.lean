module
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitComparisonHomotopy
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalFamilyHomotopy

/-!
概要：全パラメーターに整合する実錐比較を、矢印圏の四角形へ移す。
方針：元の全単体・同じ比較辺・指定頂点への錐の移送を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の第二条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma isEquivalencePathVertex_limitVertex {J X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : JoinCone p)
    (h0 : IsLimitCone (evaluateFunctorCone c (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (h1 : IsLimitCone (evaluateFunctorCone c (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (hp : ∀ j : J _⦋0⦌, IsEquivalencePathVertex (p.app (Opposite.op ⦋0⦌) j)) :
    IsEquivalencePathVertex c.vertex := by
  let H := F2.arrowFamilyHomotopy c.val
  have hj : ∀ j : J _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge H
      ((joinInr Δ[0] J).app (Opposite.op ⦋0⦌) j)).toTruncated := by
    intro j
    have he := F2.arrowFamilyHomotopy_vertex_edge c.val
      ((joinInr Δ[0] J).app (Opposite.op ⦋0⦌) j)
    have hv : c.val.app (Opposite.op ⦋0⦌)
        ((joinInr Δ[0] J).app (Opposite.op ⦋0⦌) j) = p.app (Opposite.op ⦋0⦌) j :=
      ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) j
    rw [hv] at he
    exact (isInvertibleEdge_congr he).mpr (hp j)
  have hfull := F2.Presentable.limitComparison_isInvertible_of_pointwise
    (evaluateFunctorCone c (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (evaluateFunctorCone c (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h0 h1 H hj
  have h := homotopyVertex_isInvertible_of_functorEdge H hfull
    ((joinInl Δ[0] J).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))
  have he := F2.arrowFamilyHomotopy_vertex_edge c.val
    ((joinInl Δ[0] J).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))
  have hv : c.val.app (Opposite.op ⦋0⦌)
      ((joinInl Δ[0] J).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0]))) = c.vertex := by
    rw [JoinCone.vertex_eq, SSet.yonedaEquiv_comp]
    rfl
  rw [hv] at he
  exact (isInvertibleEdge_congr he).mp h

lemma isEquivalencePathVertex_of_pointwiseLimit {J X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : JoinCone p)
    (hc : IsPointwiseLimitCone c)
    (hp : ∀ j : J _⦋0⦌, IsEquivalencePathVertex (p.app (Opposite.op ⦋0⦌) j)) :
    IsEquivalencePathVertex c.vertex :=
  isEquivalencePathVertex_limitVertex c (hc _) (hc _) hp

end SerrePositivity.InfinityCategories
