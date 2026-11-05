module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.PointedSpaceFiberVertices
public import SerrePositivity.InfinityCategories.F1.Transport.CosliceTransportPointHom

/-! # Kan 対象の等式による表示変更は、同じ指定点の分類射を輸送する -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

/-- Kan 対象の等式で移した点は、同じ等式同型による分類射の後合成。 -/
theorem pointedSpaceFiberPointHom_eq_transport {K L : KanObject.{u}} (h : K = L)
    (v : K.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv K).symm v) ≫
      (eqToIso (congrArg HomotopyCategory.mk (congrArg spaceInfinityVertex h))).hom =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv L).symm
      (Eq.mp (congrArg (fun T : KanObject.{u} => T.obj _⦋0⦌) h) v)) := by
  subst L
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.pointedSpaceFiberPointHom_eq_transport := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedSpaceFiberPointHom_eq_transport
