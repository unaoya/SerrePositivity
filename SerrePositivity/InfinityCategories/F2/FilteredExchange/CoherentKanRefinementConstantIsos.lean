module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanRefinementDegenerateEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanRefinementCancellation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.DegenerateEdgeIso

/-!
概要：元の二つの定値区間辺の類を、元の実終点の恒等同型へ戻す。
方針：実退化辺の式から両端の等式と同じ指定同型の恒等性を得る。
規約：端点の等式は実辺の二面から回収し、元の辺の類を変更しない。
使われ方：共通終点成分消去後の二つの定値因子を除去する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (K L : KanObject.{u}) (e : (SimplicialCategory.sHom K L) _⦋1⦌)
local notation "H" => SimplicialCategory.sHom K L
local notation "FL" => CategoryTheory.Functor.map SSet.uliftFunctor (edgewiseLeft H) ≫
  coherentKanLeftHomInterval K L
local notation "FR" => CategoryTheory.Functor.map SSet.uliftFunctor (edgewiseRight H) ≫
  coherentKanRightHomInterval K L
local notation "z" => ULift.up (edgewiseRefinementVertex e)
local notation "z₀" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) e))
local notation "z₁" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) e))

/-- 右解像の定値側の実始点と同じ実共通終点の像は厳密に等しい。 -/
lemma coherentKanRefinementRight_left_source_eq_target :
    (NatTrans.app FL (Opposite.op ⦋0⦌)) z₀ = (NatTrans.app FL (Opposite.op ⦋0⦌)) z :=
  degenerateEdge_source_eq_target
    ((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FL) _
    (coherentKanRefinementRight_left_degenerate K L e)

/-- 左解像の定値側も実始点と同じ実共通終点の像は厳密に等しい。 -/
lemma coherentKanRefinementLeft_right_source_eq_target :
    (NatTrans.app FR (Opposite.op ⦋0⦌)) z₁ = (NatTrans.app FR (Opposite.op ⦋0⦌)) z :=
  degenerateEdge_source_eq_target
    ((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FR) _
    (coherentKanRefinementLeft_right_degenerate K L e)

/-- 右解像の定値側の同じ辺の類は、その同じ実終点の恒等同型。 -/
lemma coherentKanRefinementRight_left_iso_heq_refl :
    HEq (edgewiseRefinementRightImageIso FL e)
      (Iso.refl (SSet.HomotopyCategory.mk ((NatTrans.app FL (Opposite.op ⦋0⦌)) z))) :=
  vertexIso_heq_refl_of_degenerate_edge _
    ((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FL) rfl _
    (coherentKanRefinementRight_left_degenerate K L e)

/-- 左解像の定値側の同じ辺の類も、その同じ実終点の恒等同型。 -/
lemma coherentKanRefinementLeft_right_iso_heq_refl :
    HEq (edgewiseRefinementLeftImageIso FR e)
      (Iso.refl (SSet.HomotopyCategory.mk ((NatTrans.app FR (Opposite.op ⦋0⦌)) z))) :=
  vertexIso_heq_refl_of_degenerate_edge _
    ((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FR) rfl _
    (coherentKanRefinementLeft_right_degenerate K L e)

end SerrePositivity.InfinityCategories.F2
