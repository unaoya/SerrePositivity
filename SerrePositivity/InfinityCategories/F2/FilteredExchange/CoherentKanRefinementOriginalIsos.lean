module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanRefinementOriginalEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanRefinementCancellation
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoEdgeRepresentatives

/-!
概要：消去式の残りの二辺の類は元の指定精密化の左右区間像の同型そのもの。
方針：実一単体の等式と同じ辺の代表を持つ指定同型の一致を使う。
規約：元の一単体の逆辺を選ばず、区間像の同じ類を保持する。
使われ方：二定値辺を除去した式を元の指定 path の作用へ戻す。
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
local notation "Y" => intervalMappingSpace (spaceInfinityVertex K) (spaceInfinityVertex L)
local notation "FL" => CategoryTheory.Functor.map SSet.uliftFunctor (edgewiseLeft H) ≫
  coherentKanLeftHomInterval K L
local notation "FR" => CategoryTheory.Functor.map SSet.uliftFunctor (edgewiseRight H) ≫
  coherentKanRightHomInterval K L

/-- 元の精密化を元の右区間へ送った同じ辺の類の同型。 -/
def coherentKanRightRefinementIso :
    VertexIso
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 1 e)))
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 0 e))) := by
  have : IsInvertibleEdge (X := Y) (coherentKanRightRefinementEdge K L e).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (coherentKanRightRefinementEdge K L e).toTruncated)

/-- 元の反転精密化を元の左区間へ送った同じ辺の類の同型。 -/
def coherentKanLeftRefinementIso :
    VertexIso
      ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm ((H).δ 0 e))))
      ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm ((H).δ 1 e)))) := by
  have : IsInvertibleEdge (X := Y) (coherentKanLeftRefinementEdge K L e).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (coherentKanLeftRefinementEdge K L e).toTruncated)

/-- 消去式の元の右辺の類は元の指定精密化の右区間像の同型と値まで一致する。 -/
lemma coherentKanRefinementRight_right_iso_heq_original :
    HEq (edgewiseRefinementRightImageIso FR e) (coherentKanRightRefinementIso K L e) :=
  vertexIso_heq_of_edge_representatives _ _
    ((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FR)
    (coherentKanRightRefinementEdge K L e) rfl rfl
    (coherentKanRefinementRight_right_edge K L e)

/-- 消去式の元の左辺の類も元の反転精密化の左区間像の同型と値まで一致する。 -/
lemma coherentKanRefinementLeft_left_iso_heq_original :
    HEq (edgewiseRefinementLeftImageIso FL e) (coherentKanLeftRefinementIso K L e) :=
  vertexIso_heq_of_edge_representatives _ _
    ((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FL)
    (coherentKanLeftRefinementEdge K L e) rfl rfl
    (coherentKanRefinementLeft_left_edge K L e)

end SerrePositivity.InfinityCategories.F2
