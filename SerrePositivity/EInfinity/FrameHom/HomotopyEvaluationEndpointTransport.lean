module

public import SerrePositivity.InfinityCategories.F1B.HomotopyRepresentative

/-!
# 全ホモトピーの評価成分と指定された同じ辺の端点輸送

概要：元の円柱の成分辺を端点等式で輸送し、同じ二胞体の評価を回収する。
方針：元の評価公式と同じ一次単体の Hom 類の輸送を合成する。
規約：始域や標的の quasicategory 性は不要。
使われ方：大きい通常複体図式の導来単位の同じ成分の照合。
-/

@[expose] public section
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

lemma functorHomEvaluate_homotopy_transport {I C : SSet.{u}} {F G : I ⟶ C}
    (H : SSet.Homotopy F G) (i : I _⦋0⦌) {x y : C _⦋0⦌}
    (hx : F.app (Opposite.op ⦋0⦌) i = x) (hy : G.app (Opposite.op ⦋0⦌) i = y)
    (e : Truncated.Edge (X := (truncation 2).obj C) x y)
    (he : (simplicialHomotopyVertexEdge H i).edge = e.edge) :
    (eqToIso (congrArg HomotopyCategory.mk hx)).inv ≫
      functorHomEvaluate (Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy H)) i ≫
      (eqToIso (congrArg HomotopyCategory.mk hy)).hom =
    Truncated.HomotopyCategory.homMk e := by
  rw [functorHomEvaluate_homotopy]
  exact homMk_transport hx hy (simplicialHomotopyVertexEdge H i).toTruncated e he

end SerrePositivity.EInfinity.FrameHom
