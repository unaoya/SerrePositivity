module

public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementOriginalSquare
public import SerrePositivity.InfinityCategories.F2.PointedIntervalValueAction

/-!
概要：元の精密化の左右区間の整合を、同じ全係数の値へ送る。
方針：既存の四同型の式に同じ普遍区間輸送と終点値を適用する。
規約：指定された比較成分を保持。使われ方：元の三角形の輸送比較との接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の左右精密化と両端比較の同じ値は四同型の整合式を満たす。 -/
lemma coherentKanRefinement_value_square (K L : KanObject.{u})
    (e : (SimplicialCategory.sHom K L) _⦋1⦌) :
    VertexIso.map (coherentKanLeftRefinementIso K L e) (pointedIntervalValueAction K L) ≪≫
      VertexIso.map (coherentKanRefinementSourceComparison K L e)
        (pointedIntervalValueAction K L) ≪≫
      VertexIso.map (coherentKanRightRefinementIso K L e) (pointedIntervalValueAction K L) =
    VertexIso.map (coherentKanRefinementTargetComparison K L e)
      (pointedIntervalValueAction K L) := by
  have h := congrArg (fun c => VertexIso.map c (pointedIntervalValueAction K L))
    (coherentKanRefinement_original_square K L e)
  simpa only [VertexIso.map, CategoryTheory.Functor.mapIso_trans] using h

end SerrePositivity.InfinityCategories.F2
