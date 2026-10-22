module

public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementOriginalIsos

/-!
概要：元の精密化の二区間辺の実両端を、共通解像の四頂点と厳密に同定する。
方針：同じ実辺の等式へ二面を適用する。
規約：HEq から頂点の等式を推測せず、元の実辺の二面を使う。
使われ方：二定値辺を除いた整合式を元の指定精密化だけの同型の等式へ戻す。
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
local notation "z" => ULift.up (edgewiseRefinementVertex e)
local notation "z₀" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) e))
local notation "z₁" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) e))

/-- 左辺の実始点は元の反転精密化の始点像。 -/
lemma coherentKanRefinement_left_source_eq_original :
    (NatTrans.app FL (Opposite.op ⦋0⦌)) z₁ =
      (coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm ((H).δ 0 e))) := by
  let a := (edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FL
  let b := coherentKanLeftRefinementEdge K L e
  have h : a.edge = b.edge := coherentKanRefinementLeft_left_edge K L e
  exact a.src_eq.symm.trans ((congrArg (SimplicialObject.δ Y (1 : Fin 2)) h).trans b.src_eq)

/-- 左辺の実終点は元の反転精密化の終点像。 -/
lemma coherentKanRefinement_left_target_eq_original :
    (NatTrans.app FL (Opposite.op ⦋0⦌)) z =
      (coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm ((H).δ 1 e))) := by
  let a := (edgewiseRefinementLeftEdgeUlift.{u, u + 1} e).map FL
  let b := coherentKanLeftRefinementEdge K L e
  have h : a.edge = b.edge := coherentKanRefinementLeft_left_edge K L e
  exact a.tgt_eq.symm.trans ((congrArg (SimplicialObject.δ Y (0 : Fin 2)) h).trans b.tgt_eq)

/-- 右辺の実始点は元の精密化の始点像。 -/
lemma coherentKanRefinement_right_source_eq_original :
    (NatTrans.app FR (Opposite.op ⦋0⦌)) z₀ =
      (coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 1 e)) := by
  let a := (edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FR
  let b := coherentKanRightRefinementEdge K L e
  have h : a.edge = b.edge := coherentKanRefinementRight_right_edge K L e
  exact a.src_eq.symm.trans ((congrArg (SimplicialObject.δ Y (1 : Fin 2)) h).trans b.src_eq)

/-- 右辺の実終点は元の精密化の終点像。 -/
lemma coherentKanRefinement_right_target_eq_original :
    (NatTrans.app FR (Opposite.op ⦋0⦌)) z =
      (coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 0 e)) := by
  let a := (edgewiseRefinementRightEdgeUlift.{u, u + 1} e).map FR
  let b := coherentKanRightRefinementEdge K L e
  have h : a.edge = b.edge := coherentKanRefinementRight_right_edge K L e
  exact a.tgt_eq.symm.trans ((congrArg (SimplicialObject.δ Y (0 : Fin 2)) h).trans b.tgt_eq)

end SerrePositivity.InfinityCategories.F2
