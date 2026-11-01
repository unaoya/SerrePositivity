module
public import SerrePositivity.InfinityCategories.Stable.FiniteShapes
public import SerrePositivity.InfinityCategories.Core.RightFibrationReflection

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

lemma isPullbackSquare_of_invertible_coneComparison {X : SSet.{u}} [Quasicategory X]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X)
    (c : JoinCone (pullbackCospan Q)) (hc : IsLimitCone c)
    (a : Truncated.Edge (X := (truncation 2).obj (sliceOver (pullbackCospan Q)))
      (pullbackCone Q) c)
    (ha : IsInvertibleEdge (a.map ((truncation 2).map
      (sliceOverProjection (pullbackCospan Q))))) : IsPullbackSquare Q := by
  have h := derived_rightFibration_reflects_invertibleEdge
    (sliceOverProjection (pullbackCospan Q)) a ha
  have : IsIso (Truncated.HomotopyCategory.homMk a) := h
  exact hc.of_vertexIso (asIso (Truncated.HomotopyCategory.homMk a)).symm

end SerrePositivity.InfinityCategories
