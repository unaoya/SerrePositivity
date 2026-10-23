module

public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleFunctorEdgePathFamily
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFamilyVertexEdge

/-!
概要：可逆 path の族を、同じ全円柱を表す関手空間の辺へ戻す。
方針：包含後の族を転置し、標準区間の辺で評価する。
規約：辺の代表を選び直さず、元の全 path を保持する。
使われ方：補正した cospan の path と元の自然性の辺の厳密な照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 可逆 path の全族を表す、両端を元の評価に揃えた同じ関手空間の辺。 -/
def equivalencePathFamilyEdge {A Y : SSet.{u}} (L : A ⟶ equivalencePath Y) :
    Edge (functorVertex (L ≫ equivalencePathEndpoint Y 0))
      (functorVertex (L ≫ equivalencePathEndpoint Y 1)) :=
  ((SSet.Edge.ofTruncated homotopyIntervalEdge).map
    (transposeFunctorFamily (L ≫ equivalencePathι Y))).ofEq
    (transposeFunctorFamily_vertex _ _) (transposeFunctorFamily_vertex _ _)

/-- 同じ path の族の辺は、そのまま転置族の Yoneda 表現。 -/
lemma equivalencePathFamilyEdge_yoneda {A Y : SSet.{u}}
    (L : A ⟶ equivalencePath Y) :
    (equivalencePathFamilyEdge L).edge =
      SSet.yonedaEquiv (transposeFunctorFamily (L ≫ equivalencePathι Y)) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  exact (congrArg ((transposeFunctorFamily (L ≫ equivalencePathι Y)).app
    (Opposite.op ⦋1⦌)) hi).symm.trans
      (SSet.yonedaEquiv_comp (𝟙 (Δ[1] : SSet.{u}))
        (transposeFunctorFamily (L ≫ equivalencePathι Y))).symm

/-- 元の可逆辺から作った同じ全 path の族は、元の一単体を厳密に回収する。 -/
lemma equivalencePathFamilyEdge_of_invertible {A Y : SSet.{u}} [Quasicategory Y]
    {f g : A ⟶ Y}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom A).obj Y))
      (functorVertex f) (functorVertex g)) (he : IsInvertibleEdge e) :
    (equivalencePathFamilyEdge (invertibleFunctorEdgePath e he)).edge = e.edge := by
  rw [equivalencePathFamilyEdge_yoneda, invertibleFunctorEdgePath_ι]
  change SSet.yonedaEquiv (transposeFunctorFamily
    (transposeFunctorFamily (SSet.yonedaEquiv.symm e.edge))) = e.edge
  rw [transposeFunctorFamily_involutive, Equiv.apply_symm_apply]

end SerrePositivity.InfinityCategories
