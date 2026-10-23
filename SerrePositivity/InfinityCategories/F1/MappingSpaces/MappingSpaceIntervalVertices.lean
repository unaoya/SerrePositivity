module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpacePrismPoint
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostIso

/-!
概要：左右の写像空間から区間模型への比較の零単体を元の辺で表示する。
方針：一点の prism の式と Yoneda 射の uncurry を使う。
規約：端点の順序を保ち、充填性を仮定しない。
使われ方：pointed fiber の指定頂点を右 Hom の点評価で回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 辺の区間頂点の Yoneda 族は、時間座標に元の辺を続けた族。 -/
lemma intervalMappingVertexOfEdge_uncurry {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) :
    intervalMappingUncurry (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge e)) =
      fst (Δ[1] : SSet.{u}) Δ[0] ≫ SSet.yonedaEquiv.symm e.edge := by
  unfold intervalMappingUncurry
  rw [SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm
    (functorVertex (SSet.yonedaEquiv.symm e.edge))) = _
  rw [SSet.yonedaEquiv_symm_zero, uncurry_const_functorVertex]

/-- coslice の区間比較の零単体は、同じ錐から取り出した辺の区間頂点。 -/
lemma cosliceFiberToIntervalMappingSpace_vertex {X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) _⦋0⦌) :
    (cosliceFiberToIntervalMappingSpace x y).app _ s =
      intervalMappingVertexOfEdge (cosliceFiberVertexToEdge s) := by
  apply SSet.yonedaEquiv.symm.injective
  apply intervalMappingUncurry_injective
  rw [← SSet.yonedaEquiv_symm_comp, cosliceFiberToIntervalMappingSpace_uncurry,
    intervalMappingVertexOfEdge_uncurry, leftMappingSpacePrism_point,
    rightMappingSpacePrism_point, Category.assoc]
  unfold cosliceFiberUncurry
  rw [SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda]
  change _ = fst (Δ[1] : SSet.{u}) Δ[0] ≫
    SSet.yonedaEquiv.symm (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ s.val.val))
  rw [Equiv.symm_apply_apply]
  rfl

/-- 右 pinched 比較の零単体は、元の一単体が表す辺の区間頂点。 -/
lemma pinchedHomToIntervalMappingSpace_vertex {X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (pinchedHom x y) _⦋0⦌) :
    (pinchedHomToIntervalMappingSpace x y).app _ s =
      intervalMappingVertexOfEdge (pinchedHomVertexEquiv x y s) := by
  apply SSet.yonedaEquiv.symm.injective
  apply intervalMappingUncurry_injective
  rw [← SSet.yonedaEquiv_symm_comp, pinchedHomToIntervalMappingSpace_uncurry,
    intervalMappingVertexOfEdge_uncurry, rightMappingSpacePrism_point, Category.assoc]
  unfold pinchedHomUncurry
  rw [SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda]
  change fst (Δ[1] : SSet.{u}) Δ[0] ≫ (joinStdSimplexIso 0 0).inv ≫
    ((joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm s.val) = _
  rw [Iso.inv_hom_id_assoc]
  rfl

/-- 端点を正規化した後合成の零単体は、同じ辺の像を端点表示ごと移す。 -/
lemma intervalMappingPostOfEq_vertex {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌} (hx : f.app _ x = x') (hy : f.app _ y = y')
    (e : X.Edge x y) :
    (intervalMappingPostOfEq f x y hx hy).app _ (intervalMappingVertexOfEdge e) =
      intervalMappingVertexOfEdge ((e.map f).ofEq hx hy) := by
  apply SSet.yonedaEquiv.symm.injective
  apply intervalMappingUncurry_injective
  rw [← SSet.yonedaEquiv_symm_comp, intervalMappingPostOfEq_uncurry,
    intervalMappingVertexOfEdge_uncurry, intervalMappingVertexOfEdge_uncurry,
    Category.assoc]
  change _ = fst (Δ[1] : SSet.{u}) Δ[0] ≫ SSet.yonedaEquiv.symm (f.app _ e.edge)
  rw [← SSet.yonedaEquiv_symm_comp]

end SerrePositivity.InfinityCategories
