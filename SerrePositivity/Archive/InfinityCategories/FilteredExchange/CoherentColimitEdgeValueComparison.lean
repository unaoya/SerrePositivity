module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitEdgeNativeComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceEdgeValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanFixedSquareIso

/-!
概要：元の余極限指定辺と native 区間表示の Kan 値を、同じ比較円柱から比較する。
方針：元の四辺を厳密に合わせ、その全円柱の二三角形の精密化同型を合成する。
規約：辺の類から別の円柱を選ばない。使われ方：二三角形・指定 path の全錐比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の余極限指定辺の、その始域余錐の頂点の Kan 値を始域とする実際の射。 -/
def coherentColimitEdgeValue :=
  spaceInfinityEdgeValue (SSet.Edge.ofTruncated (coherentColimitAdjustedEdge B H))

/-- 選択済み native 辺の区間表示の、同じ両端の Kan 値の間の実際の射。 -/
def coherentColimitNativeIntervalValue :=
  spaceInfinityEdgeValue (intervalMappingEdgeOfVertex (coherentColimitNativeIntervalVertex B H))

/-- 元の比較円柱の上下二単体を保つ、元の二辺の Kan 値の指定比較同型。 -/
def coherentColimitEdgeValueNativeIso : FunctorIso (coherentColimitEdgeValue B H)
    (coherentColimitNativeIntervalValue B H) := by
  let Q := coherentColimitIntervalNativeHomotopy B H
  apply kanFixedSquareValueIso (coherentColimitEdgeValue B H)
    (coherentColimitNativeIntervalValue B H) Q.h
  · calc
      SSet.yonedaEquiv (SSet.ι₀ ≫ Q.h) = (coherentColimitFunctorEdge B H).edge := by
        rw [Q.h₀]
        exact Equiv.apply_symm_apply _ _
      _ = _ := (spaceInfinityEdgeValue_edge
        (SSet.Edge.ofTruncated (coherentColimitAdjustedEdge B H))).symm
  · rw [Q.h₁]
    exact (spaceInfinityEdgeValue_edge
      (intervalMappingEdgeOfVertex (coherentColimitNativeIntervalVertex B H))).symm
  · rw [coherentColimitIntervalNativeHomotopy_source]
    exact (spaceInfinityIdentity_edge _).symm
  · rw [coherentColimitIntervalNativeHomotopy_target]
    exact (spaceInfinityIdentity_edge _).symm

end SerrePositivity.InfinityCategories.F2
