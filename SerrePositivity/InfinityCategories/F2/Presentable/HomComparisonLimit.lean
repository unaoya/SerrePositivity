module

public import SerrePositivity.InfinityCategories.F1.Presentable.LimitComparisonHomotopy
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：元の全比較の可逆成分は、両側が保存する同じ極限で閉じている。
方針：指定された全錐へ比較を制限し、普遍錐の射影による反映を使う。
規約：元の射・全ホモトピー・全錐を保持。極限存在を追加の instance へ隠さない。
使われ方：Ind 比較の始域の単一 filtered 表示への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 両側が保存する同じ全錐上で、比較の可逆性は図式から極限頂点へ延長する。 -/
lemma homotopyComparison_limit_vertex {J C X : SSet.{u}} [Quasicategory X]
    {D : J ⟶ C} (c : JoinCone D) {F G : C ⟶ X} (H : SSet.Homotopy F G)
    (hF : IsLimitCone (mapJoinCone F c)) (hG : IsLimitCone (mapJoinCone G c))
    (hH : ∀ j : J _⦋0⦌, IsInvertibleEdge
      (simplicialHomotopyVertexEdge H (D.app (Opposite.op ⦋0⦌) j)).toTruncated) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H c.vertex).toTruncated := by
  let Hc := stableHomotopyPrecomp c.val H
  have hb : ∀ j : J _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge Hc
      ((joinInr Δ[0] J).app (Opposite.op ⦋0⦌) j)).toTruncated := by
    intro j
    have hv : c.val.app (Opposite.op ⦋0⦌)
        ((joinInr Δ[0] J).app (Opposite.op ⦋0⦌) j) = D.app (Opposite.op ⦋0⦌) j :=
      ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) j
    have he := homotopyVertexEdge_precomp c.val H
      ((joinInr Δ[0] J).app (Opposite.op ⦋0⦌) j)
    rw [hv] at he
    exact (isInvertibleEdge_congr he).mpr (hH j)
  have hi := limitComparison_isInvertible_of_pointwise
    (mapJoinCone F c) (mapJoinCone G c) hF hG Hc hb
  have ht := homotopyVertex_isInvertible_of_functorEdge Hc hi
    ((joinInl Δ[0] J).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))
  have he := homotopyVertexEdge_precomp c.val H
    ((joinInl Δ[0] J).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))
  have hv : c.val.app (Opposite.op ⦋0⦌)
      ((joinInl Δ[0] J).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0]))) = c.vertex := by
    rw [JoinCone.vertex_eq, SSet.yonedaEquiv_comp]
    rfl
  rw [hv] at he
  exact (isInvertibleEdge_congr he).mp ht

/-- 元の関手圏の射の可逆成分条件は、両側が保存する同じ指定極限で閉じている。 -/
lemma functorHomComparison_limit_vertex {J C X : SSet.{u}} [Quasicategory X]
    {D : J ⟶ C} (c : JoinCone D) {F G : C ⟶ X}
    (t : (HomotopyCategory.mk (functorVertex F) : hoFunctor.obj ((ihom C).obj X)) ⟶
      HomotopyCategory.mk (functorVertex G))
    (hF : IsLimitCone (mapJoinCone F c)) (hG : IsLimitCone (mapJoinCone G c))
    (ht : ∀ j : J _⦋0⦌, IsIso ((hoFunctor.map
      (evaluateFunctorAt (Y := X) (D.app (Opposite.op ⦋0⦌) j))).toFunctor.map t)) :
    IsIso ((hoFunctor.map (evaluateFunctorAt (Y := X) c.vertex)).toFunctor.map t) := by
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective (functorVertex F) (functorVertex G) t
  let H := simplicialHomotopyOfFunctorEdge e
  have hEval (a : C _⦋0⦌) :
      IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated ↔
        IsIso ((hoFunctor.map (evaluateFunctorAt (Y := X) a)).toFunctor.map t) := by
    rw [← he]
    exact isInvertibleEdge_congr (evaluateFunctorAt_edge e a)
  exact (hEval c.vertex).mp (homotopyComparison_limit_vertex c H hF hG
    (fun j ↦ (hEval _).mpr (ht j)))

end SerrePositivity.InfinityCategories.F2.Presentable
