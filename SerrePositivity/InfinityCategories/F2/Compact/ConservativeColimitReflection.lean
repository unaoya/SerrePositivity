module

public import SerrePositivity.InfinityCategories.F2.Compact.ColimitComparisonApex

/-!
概要：辺の可逆性を反映する関手は、保存された基準余極限があれば元の余極限性を反映。
方針：元の基準余錐から指定余錐への比較辺の頂点像を反映し、実余錐内で可逆に戻す。
規約：元の全余錐と同じ関手の像を使う。
使われ方：Ind-S の指定された空間の宇宙変更による小余極限の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
/-- 概要：元の保存された基準余極限と辺の可逆性の反映から、指定全余錐の余極限性。
方針：元の比較辺を実 coslice 内で反映。規約：元の両余錐。使われ方：宇宙変更の反映。 -/
lemma isColimitCone_of_conservative_image {J X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y)
    (hF : ∀ {a b : X _⦋0⦌} (e : X.Edge a b), IsInvertibleEdge (e.map F) → IsInvertibleEdge e)
    {D : J ⟶ X} (d c : JoinCocone D) (hd : IsColimitCone d)
    (hFd : IsColimitCone (mapJoinCocone F d)) (hFc : IsColimitCone (mapJoinCocone F c)) :
    IsColimitCone c := by
  obtain ⟨e₀⟩ := IsInitialVertex.nonempty_edge (X := sliceUnder D) hd c
  let e := SSet.Edge.ofTruncated (X := sliceUnder D) e₀
  have ha := hF (colimitComparisonApexEdge e) (colimitComparisonApex_map_isInvertible F hFd hFc e)
  have he : IsInvertibleEdge (X := sliceUnder D) e.toTruncated :=
    leftFibration_reflects_invertibleEdge (sliceUnderProjection D) e.toTruncated ha
  have : IsIso (SSet.HomotopyCategory.homMk e) := he
  exact hd.of_vertexIso (asIso (SSet.HomotopyCategory.homMk e))
end SerrePositivity.InfinityCategories.F2.Compact
