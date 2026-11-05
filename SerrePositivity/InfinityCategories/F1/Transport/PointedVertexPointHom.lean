module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.PointedFamilyPointHom

/-! # 元の pointed-space 頂点の点の射を、同じ指定 fiber の端点で読む -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- pointed-space 頂点を元の指定 fiber の表示へ戻しても、同じ点の辺の類を保持する。 -/
theorem pointedVertexPointHom_fiber {b : SpaceInfinity.{u} _⦋0⦌}
    (s : (vertexFiber pointedSpaceProjection b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom s.val ≫
      (eqToIso (congrArg HomotopyCategory.mk (s.property.trans (pinchedConstant_zero b)))).hom =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom s := by
  have he := homMk_transport (rfl : pointSpaceVertex = pointSpaceVertex)
    (s.property.trans (pinchedConstant_zero b))
    (cosliceFiberVertexToEdge (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexFiberPoint s.val)).toTruncated
    (cosliceFiberVertexToEdge s).toTruncated rfl
  simpa only [_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom, _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom, eqToIso.hom,
    eqToHom_refl, Category.id_comp] using he

/-- 点と底の値の表示を二段階で揃えても、同じ指定 fiber 点の射を回収する。 -/
theorem pointedVertexPointHom_transport {b c : SpaceInfinity.{u} _⦋0⦌}
    (t : (vertexFiber pointedSpaceProjection b) _⦋0⦌)
    (s : PointedSpaceInfinity.{u} _⦋0⦌) (hs : s = t.val)
    (hc : pointedSpaceProjection.app (Opposite.op ⦋0⦌) s = c) (hb : c = b) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom s ≫ (eqToIso (congrArg HomotopyCategory.mk hc)).hom ≫
      (eqToIso (congrArg HomotopyCategory.mk hb)).hom = _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom t := by
  cases hs
  have hc' : (eqToIso (congrArg HomotopyCategory.mk hc)).hom ≫
      (eqToIso (congrArg HomotopyCategory.mk hb)).hom =
      (eqToIso (congrArg HomotopyCategory.mk
        (t.property.trans (pinchedConstant_zero b)))).hom :=
    eqToHom_trans (congrArg HomotopyCategory.mk hc) (congrArg HomotopyCategory.mk hb)
  exact (congrArg (fun m => _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom t.val ≫ m) hc').trans
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom_fiber t)

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedVertexPointHom_fiber := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom_fiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedVertexPointHom_transport := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom_transport
