module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ColimitHomotopyPointwise
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：同じ全自然な比較が図式上で可逆なら、両側が保つ同じ余極限頂点でも可逆。
方針：元の余錐全体に比較を制限し、F2 の普遍余錐の比較の可逆性へ渡す。
規約：元の全ホモトピーと全余錐を保持。余極限存在や比較の可逆性は隠さない。
使われ方：κ-compact 性による Ind 比較の生成対象から任意対象への拡張。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 両側が保つ同じ指定余錐について、比較の可逆性は図式から頂点へ延長する。 -/
lemma homotopyComparison_colimit_vertex {J C X : SSet.{u}} [Quasicategory X]
    {D : J ⟶ C} (c : JoinCocone D) {F G : C ⟶ X} (H : SSet.Homotopy F G)
    (hF : IsColimitCone (mapJoinCocone F c)) (hG : IsColimitCone (mapJoinCocone G c))
    (hH : ∀ j : J _⦋0⦌, IsInvertibleEdge
      (simplicialHomotopyVertexEdge H (D.app (Opposite.op ⦋0⦌) j)).toTruncated) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H c.vertex).toTruncated := by
  let Hc := stableHomotopyPrecomp c.val H
  have hb : ∀ j : J _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge Hc
      ((joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j)).toTruncated := by
    intro j
    have hv : c.val.app (Opposite.op ⦋0⦌)
        ((joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j) = D.app (Opposite.op ⦋0⦌) j :=
      ConcreteCategory.congr_hom (NatTrans.congr_app c.property (Opposite.op ⦋0⦌)) j
    have he := homotopyVertexEdge_precomp c.val H
      ((joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j)
    rw [hv] at he
    exact (isInvertibleEdge_congr he).mpr (hH j)
  have ht := colimitHomotopy_vertex_isInvertible
    (mapJoinCocone F c) (mapJoinCocone G c) hF hG Hc hb
  have he := homotopyVertexEdge_precomp c.val H
    ((joinInr J Δ[0]).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))
  have hv : c.val.app (Opposite.op ⦋0⦌)
      ((joinInr J Δ[0]).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0]))) = c.vertex := by
    rw [JoinCocone.vertex_eq, SSet.yonedaEquiv_comp]
    rfl
  rw [hv] at he
  exact (isInvertibleEdge_congr he).mp ht

end SerrePositivity.InfinityCategories.F2.Presentable
