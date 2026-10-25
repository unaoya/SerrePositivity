module

public import SerrePositivity.InfinityCategories.F2.Compact.LimitComparisonApex
public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleCartesian

/-!
概要：辺の可逆性を反映する関手は、保存された基準極限があれば元の極限性を反映。
方針：元の比較辺の頂点像を反映し、slice 射影の cartesian 辺から錐内へ戻す。
規約：元の全錐と同じ関手の像を使う。
使われ方：Ind-S の指定された空間の宇宙変更による小極限の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
/-- 概要：保存された基準極限と辺の可逆性の反映から、元の指定全錐の極限性。
方針：元の比較辺を slice 内で反映。規約：元の両錐。使われ方：宇宙変更の反映。 -/
lemma isLimitCone_of_conservative_image {J X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (hF : ∀ {a b : X _⦋0⦌} (e : X.Edge a b), IsInvertibleEdge (e.map F) → IsInvertibleEdge e)
    {D : J ⟶ X} (d c : JoinCone D) (hd : IsLimitCone d)
    (hFd : IsLimitCone (mapJoinCone F d)) (hFc : IsLimitCone (mapJoinCone F c)) :
    IsLimitCone c := by
  obtain ⟨e₀⟩ := IsTerminalVertex.nonempty_edge (X := sliceOver D) hd c
  let e := SSet.Edge.ofTruncated (X := sliceOver D) e₀
  have ha := hF (limitComparisonApexEdge e) (limitComparisonApex_map_isInvertible F hFc hFd e)
  have he : IsInvertibleEdge (X := sliceOver D) e.toTruncated :=
    isInvertibleEdge_of_isCartesianEdge (sliceOverProjection D) e.toTruncated
      (isCartesianEdge_of_rightFibration (sliceOverProjection D) e.edge) ha
  have : IsIso (SSet.HomotopyCategory.homMk e) := he
  exact hd.of_vertexIso (asIso (SSet.HomotopyCategory.homMk e)).symm

end SerrePositivity.InfinityCategories.F2.Compact
