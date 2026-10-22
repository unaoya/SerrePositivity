module

public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyTransformationVertex
public import SerrePositivity.InfinityCategories.F1.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：元の円柱からの指定変換頂点は、図式の制限と厳密に可換する。
方針：区間写像空間の実際の後合成の頂点公式と curry の前合成自然性を用いる。
規約：制限後の両端は指定された図式の等式で正規化する。
使われ方：密度の大域変換を元の写像空間比較の底変換へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 指定変換頂点を円柱へ戻してから読み直すと同じ頂点。 -/
lemma homotopyTransformationVertex_recovered {K X : SSet.{u}} {f g : K ⟶ X}
    (t : (intervalMappingSpace (functorVertex f) (functorVertex g)) _⦋0⦌) :
    homotopyTransformationVertex (simplicialHomotopyOfFunctorEdge
      (intervalMappingEdgeOfVertex t).toTruncated) = t := by
  unfold homotopyTransformationVertex
  have he := (intervalMappingEdgeVertexEquiv (functorVertex f)
    (functorVertex g)).apply_symm_apply t
  convert he using 1
  apply congrArg intervalMappingVertexOfEdge
  apply SSet.Edge.ext
  change SSet.yonedaEquiv (curry (uncurry
    (SSet.yonedaEquiv.symm (intervalMappingEdgeOfVertex t).edge))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]
  rfl

/-- 指定円柱の変換頂点を底で制限すると、同じ制限円柱の指定頂点。 -/
lemma homotopyTransformationVertex_restriction {A B X : SSet.{u}}
    {f g : B ⟶ X} {f' g' : A ⟶ X} (H : SSet.Homotopy f g) (k : A ⟶ B)
    (hf : k ≫ f = f') (hg : k ≫ g = g') (H' : SSet.Homotopy f' g')
    (hH : H'.h = (k ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    (intervalMappingPostOfEq ((pre k).app X) (functorVertex f) (functorVertex g)
      (congrArg functorVertex hf) (congrArg functorVertex hg)).app (Opposite.op ⦋0⦌)
        (homotopyTransformationVertex H) = homotopyTransformationVertex H' := by
  unfold homotopyTransformationVertex
  rw [intervalMappingPostOfEq_vertex]
  apply congrArg intervalMappingVertexOfEdge
  apply SSet.Edge.ext
  change ((pre k).app X).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
    SSet.yonedaEquiv (curry H'.h)
  rw [← SSet.yonedaEquiv_comp, curry_pre_app, hH]

end SerrePositivity.InfinityCategories.F2.Ind
