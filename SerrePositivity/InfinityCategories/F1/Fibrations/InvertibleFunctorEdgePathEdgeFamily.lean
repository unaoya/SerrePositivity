module

public import SerrePositivity.InfinityCategories.F1.Fibrations.InvertibleFunctorEdgePathFamily

/-!
概要：指定された辺の型を保持して、元の可逆 path の族を回収する。
方針：辺全体を受け取る補題で、端点の大きい定義の展開を分離する。
規約：同じ辺と同じ全高次の族を保持する。
使われ方：元の底変換比較の可逆 path の厳密な回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の辺の端点表示を保持した、同じ可逆 path の区間族への回収。 -/
lemma invertibleFunctorEdgePath_ι_of_edge_family {A Y : SSet.{u}} [Quasicategory Y]
    {f g : A ⟶ Y} (e : SSet.Edge (functorVertex f) (functorVertex g))
    (he : IsInvertibleEdge e.toTruncated)
    (F : A ⟶ (ihom (Δ[1] : SSet.{u})).obj Y)
    (hF : SSet.yonedaEquiv (transposeFunctorFamily F) = e.edge) :
    invertibleFunctorEdgePath e.toTruncated he ≫ equivalencePathι Y = F :=
  invertibleFunctorEdgePath_ι_of_family e.toTruncated he F hF

end SerrePositivity.InfinityCategories
