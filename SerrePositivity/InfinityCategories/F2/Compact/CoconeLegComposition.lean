module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegEdge
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpaceTriangleFaces
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.SpaceEdgeValue

/-!
概要：元の余錐間の辺の可換三角形を、同じ脚の Kan 値の合成ホモトピーへ移す。
方針：元の legCompStruct の同じ二単体を、全三辺の読み戻しで正規化する。
規約：底の図式も両余錐も全三角形も変更しない。
使われ方：標準余極限余錐の点回収を任意の指定余極限余錐へ移送する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}} {c d : JoinCocone F}

/-- 元の余錐間の同じ辺を、指定された元の両頂点間の辺へ射影する。 -/
def coconeVertexEdge
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder F)) c d) :
    SpaceInfinity.{u}.Edge c.vertex d.vertex :=
  SSet.Edge.ofTruncated (e.map ((truncation 2).map (sliceUnderProjection F)))

/-- 元の余錐の可換三角形は、同じ脚と頂点辺の Kan 値の合成をホモトピーまで保つ。 -/
def coconeLegCompositionHomotopy
    (e : SSet.Truncated.Edge (X := (truncation 2).obj (sliceUnder F)) c d)
    (b : B _⦋0⦌) :
    SSet.Homotopy (spaceInfinityEdgeValue (coconeTransportLeg d b))
      (spaceInfinityEdgeValue (coconeTransportLeg c b) ≫
        spaceInfinityEdgeValue (coconeVertexEdge e)) := by
  let t := c.legCompStruct e (SSet.yonedaEquiv.symm b)
  apply spaceInfinityTriangleHomotopy_of_faces _ _ _ t.simplex
  · rw [spaceInfinityEdgeValue_edge, coconeTransportLeg_edge]
    exact t.d₂
  · rw [spaceInfinityEdgeValue_edge]
    exact t.d₀
  · rw [spaceInfinityEdgeValue_edge, coconeTransportLeg_edge]
    exact t.d₁

end SerrePositivity.InfinityCategories.F2.Compact
