module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanRefinementIntervalEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.LiftedConstantEdgeImage

/-!
概要：二自然性正方形に現れた二つの定値区間辺を元の端点像の退化辺へ戻す。
方針：実辺全体の四射影の式と、定値引き戻しの像の退化辺の式を合成する。
規約：元の実辺と同じ左右区間族、同じ実端点を保持する。
使われ方：共通成分消去後の二つの定値辺の類を除去する。
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

/-- 右自然性の定値側の実区間辺は元の始点像における同じ退化辺。 -/
lemma coherentKanRefinementRight_left_degenerate :
    ((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FL).edge =
      SimplicialObject.σ Y (0 : Fin 1)
        ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm ((SimplicialCategory.sHom K L).δ 1 e)))) := by
  rw [coherentKanRefinementRight_left_edge]
  exact liftedOppositeConstantSimplexPullback_image_degenerate
    (coherentKanLeftHomInterval K L) e 0

/-- 左自然性の定値側の実区間辺は元の終点像における同じ退化辺。 -/
lemma coherentKanRefinementLeft_right_degenerate :
    ((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FR).edge =
      SimplicialObject.σ Y (0 : Fin 1)
        ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
          (ULift.up ((SimplicialCategory.sHom K L).δ 0 e))) := by
  rw [coherentKanRefinementLeft_right_edge]
  exact liftedConstantSimplexPullback_image_degenerate
    (coherentKanRightHomInterval K L) e 1

end SerrePositivity.InfinityCategories.F2
