module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanRefinementNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementLiftedProjections

/-!
概要：指定左右区間比較の自然性に使った実辺の像を、元の精密化の像へ厳密に戻す。
方針：同じ持ち上げた四射影を元の左右区間族で写す。
規約：元の実一単体と定値辺を変更しない。
使われ方：二正方形の共通成分を消去して元の指定 path の作用を照合する。
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

/-- 右自然性の右辺の実辺は元の精密化を元の右区間族へ写した辺。 -/
lemma coherentKanRefinementRight_right_edge :
    ((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FR).edge =
      (coherentKanRightHomInterval K L).app (Opposite.op ⦋1⦌) (ULift.up e) :=
  congrArg ((coherentKanRightHomInterval K L).app (Opposite.op ⦋1⦌))
    (edgewiseRefinementRightEdgeUlift_right.{u, u + 1} e)

/-- 左自然性の左辺の実辺は元の反転精密化を元の左区間族へ写した辺。 -/
lemma coherentKanRefinementLeft_left_edge :
    ((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FL).edge =
      (coherentKanLeftHomInterval K L).app (Opposite.op ⦋1⦌)
        (ULift.up (SSet.opObjEquiv.symm e)) :=
  congrArg ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋1⦌))
    (edgewiseRefinementLeftEdgeUlift_left.{u, u + 1} e)

/-- 右自然性の残りの実辺は元の始点に定値な係数の左区間族の像。 -/
lemma coherentKanRefinementRight_left_edge :
    ((edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FL).edge =
      (coherentKanLeftHomInterval K L).app (Opposite.op ⦋1⦌)
        (ULift.up (SSet.opObjEquiv.symm
          (CategoryTheory.Functor.map H (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e))) :=
  congrArg ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋1⦌))
    (edgewiseRefinementRightEdgeUlift_left.{u, u + 1} e)

/-- 左自然性の残りの実辺は元の終点に定値な係数の右区間族の像。 -/
lemma coherentKanRefinementLeft_right_edge :
    ((edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FR).edge =
      (coherentKanRightHomInterval K L).app (Opposite.op ⦋1⦌)
        (ULift.up (CategoryTheory.Functor.map H (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e)) :=
  congrArg ((coherentKanRightHomInterval K L).app (Opposite.op ⦋1⦌))
    (edgewiseRefinementLeftEdgeUlift_right.{u, u + 1} e)

end SerrePositivity.InfinityCategories.F2
