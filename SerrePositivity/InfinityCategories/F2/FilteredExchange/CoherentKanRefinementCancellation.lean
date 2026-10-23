module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanRefinementIntervalEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgewiseRefinementIsoSquares

/-!
概要：F1 の元の左右区間比較の二自然性正方形から、同じ共通終点成分を消去する。
方針：元の四つの実辺の類と二つの定値成分を保持して一般の消去式を適用する。
規約：元の Kan Hom の指定精密化を変更しない。
使われ方：残る二つの定値辺を除去し、元の反転側と右側の精密化の作用を照合する。
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
local notation "T" => coherentKanTwoSidedIntervalIso K L
local notation "S₀" => FunctorIso.app T (ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) e)))
local notation "S₁" => FunctorIso.app T (ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) e)))

/-- 元の左右区間比較の同じ共通終点成分は、元の四辺の類を保持して消去できる。 -/
lemma coherentKanRefinement_common_component_cancel :
    edgewiseRefinementLeftImageIso FL e ≪≫
        (edgewiseRefinementRightImageIso FL e).symm ≪≫ S₀ ≪≫
          edgewiseRefinementRightImageIso FR e =
      S₁ ≪≫ edgewiseRefinementLeftImageIso FR e :=
  edgewiseRefinement_common_component_cancel (coherentKanTwoSidedIntervalIso K L) e

end SerrePositivity.InfinityCategories.F2
