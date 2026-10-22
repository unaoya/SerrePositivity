module
public import SerrePositivity.KST.Fibration.PointedFamilyPointHom

/-! # 元の pointed-space 頂点の点の射を、同じ指定 fiber の端点で読む -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- pointed-space 頂点を元の指定 fiber の表示へ戻しても、同じ点の辺の類を保持する。 -/
theorem pointedVertexPointHom_fiber {b : SpaceInfinity.{u} _⦋0⦌}
    (s : (vertexFiber pointedSpaceProjection b) _⦋0⦌) :
    pointedVertexPointHom s.val ≫
      (eqToIso (congrArg HomotopyCategory.mk (s.property.trans (pinchedConstant_zero b)))).hom =
      cosliceFiberPointHom s := by
  have he := homMk_transport (rfl : pointSpaceVertex = pointSpaceVertex)
    (s.property.trans (pinchedConstant_zero b))
    (cosliceFiberVertexToEdge (pointedVertexFiberPoint s.val)).toTruncated
    (cosliceFiberVertexToEdge s).toTruncated rfl
  simpa only [pointedVertexPointHom, cosliceFiberPointHom, eqToIso.hom,
    eqToHom_refl, Category.id_comp] using he

/-- 点と底の値の表示を二段階で揃えても、同じ指定 fiber 点の射を回収する。 -/
theorem pointedVertexPointHom_transport {b c : SpaceInfinity.{u} _⦋0⦌}
    (t : (vertexFiber pointedSpaceProjection b) _⦋0⦌)
    (s : PointedSpaceInfinity.{u} _⦋0⦌) (hs : s = t.val)
    (hc : pointedSpaceProjection.app (Opposite.op ⦋0⦌) s = c) (hb : c = b) :
    pointedVertexPointHom s ≫ (eqToIso (congrArg HomotopyCategory.mk hc)).hom ≫
      (eqToIso (congrArg HomotopyCategory.mk hb)).hom = cosliceFiberPointHom t := by
  cases hs
  have hc' : (eqToIso (congrArg HomotopyCategory.mk hc)).hom ≫
      (eqToIso (congrArg HomotopyCategory.mk hb)).hom =
      (eqToIso (congrArg HomotopyCategory.mk
        (t.property.trans (pinchedConstant_zero b)))).hom :=
    eqToHom_trans (congrArg HomotopyCategory.mk hc) (congrArg HomotopyCategory.mk hb)
  exact (congrArg (fun m => pointedVertexPointHom t.val ≫ m) hc').trans
    (pointedVertexPointHom_fiber t)

end SerrePositivity.KST.Fibration
