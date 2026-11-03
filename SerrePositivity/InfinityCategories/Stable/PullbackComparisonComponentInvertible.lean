module
public import SerrePositivity.InfinityCategories.Stable.FunctorPullbackComparisonEvaluation
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.SquareConePostcomp

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

lemma functorPullbackComparison_component_isInvertible {K X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X)
    (c : JoinCone (pullbackCospan Q)) (hc : IsLimitCone c) (k : K _⦋0⦌)
    (hQ : IsPullbackSquare (Q ≫ evaluateFunctorAt k)) :
    IsInvertibleEdge ((functorPullbackComparisonEdge Q c hc).map
      ((truncation 2).map (evaluateFunctorAt k))) := by
  let f := evaluateFunctorAt (Y := X) k
  let e := functorPullbackConeComparisonEdge Q c hc
  let e' : Truncated.Edge (X := (truncation 2).obj (sliceOver (pullbackCospan Q ≫ f)))
      (mapJoinCone f (pullbackCone Q)) (mapJoinCone f c) :=
    e.map ((truncation 2).map (sliceOverPostcomp (pullbackCospan Q) f))
  have h0 : IsLimitCone (mapJoinCone f (pullbackCone Q)) :=
    (F2.isLimitCone_map_pullbackCone_iff f Q).mpr hQ
  have h1 : IsLimitCone (mapJoinCone f c) := functorPullbackComparison_target_pointwise Q c hc k
  have he : IsInvertibleEdge e' := isIso_of_isTerminal h0.isTerminalHo h1.isTerminalHo _
  have h := he.map (sliceOverProjection (pullbackCospan Q ≫ f))
  change IsInvertibleEdge
    ((functorPullbackComparisonEdge Q c hc).map ((truncation 2).map f)) at h
  exact h

end SerrePositivity.InfinityCategories
