module

public import SerrePositivity.InfinityCategories.F2.Compact.ColimitComparisonApex
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.F1B.Cones.SliceProjectionLaws

/-!
概要：元の指定錐間の比較辺は、両像が極限なら像の頂点で可逆。
方針：同じ錐辺を slice 後合成で写し、終対象間の可逆性を射影する。
規約：元の比較辺と同じ後合成射を保持する。
使われ方：Ind-S の宇宙変更に沿う小極限の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
/-- 概要：元の錐辺を同じ頂点の辺へ射影する。
方針：slice 射影。規約：元の辺。使われ方：極限比較の反映。 -/
def limitComparisonApexEdge {J X : SSet.{u}} {p : J ⟶ X} {c d : JoinCone p}
    (e : (sliceOver p).Edge c d) : X.Edge c.vertex d.vertex :=
  e.map (sliceOverProjection p)

/-- 概要：元の両錐像が極限なら同じ比較辺の頂点像は可逆。
方針：終対象間の辺を射影。規約：元の辺。使われ方：保守的な極限反映。 -/
lemma limitComparisonApex_map_isInvertible {J X Y : SSet.{u}} [Quasicategory Y]
    {p : J ⟶ X} (q : X ⟶ Y) {c d : JoinCone p}
    (hc : IsLimitCone (mapJoinCone q c)) (hd : IsLimitCone (mapJoinCone q d))
    (e : (sliceOver p).Edge c d) :
    IsInvertibleEdge ((limitComparisonApexEdge e).map q) := by
  let e' := e.map (sliceOverPostcomp p q)
  have hi : IsInvertibleEdge e' := isIso_of_isTerminal hc.isTerminalHo hd.isTerminalHo _
  have h := hi.map (sliceOverProjection (p ≫ q))
  have he : (e'.map (sliceOverProjection (p ≫ q))).edge =
      ((limitComparisonApexEdge e).map q).edge := by
    exact congrArg (fun f : sliceOver p ⟶ Y ↦ f.app (Opposite.op ⦋1⦌) e.edge)
      (F1B.sliceOverPostcomp_projection p q)
  exact (isInvertibleEdge_congr he).mp h

end SerrePositivity.InfinityCategories.F2.Compact
