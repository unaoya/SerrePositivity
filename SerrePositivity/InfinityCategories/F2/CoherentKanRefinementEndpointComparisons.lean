module

public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementOriginalVertices
public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementReducedSquare

/-!
概要：元の F1 の両端成分を元の精密化の左右区間の同じ端点間の同型へ表示変更する。
方針：実辺から回収した四頂点の等式だけで成分の両端を揃える。
規約：元の指定成分の値を保持する。
使われ方：元の指定精密化の二つの区間像だけによる整合式。
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
local notation "T" => coherentKanTwoSidedIntervalIso K L
local notation "z₀" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) e))
local notation "z₁" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) e))

/-- 始点側の元の指定成分を同じ元の左右区間の始点像の比較として保持する。 -/
def coherentKanRefinementSourceComparison :
    VertexIso
      ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm ((H).δ 1 e))))
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 1 e))) :=
  vertexIsoOfEq (FunctorIso.app T z₀)
    ((coherentKanRefinementRight_left_source_eq_target K L e).trans
      (coherentKanRefinement_left_target_eq_original K L e))
    (coherentKanRefinement_right_source_eq_original K L e)

/-- 終点側の元の指定成分も同じ元の左右区間の終点像の比較として保持する。 -/
def coherentKanRefinementTargetComparison :
    VertexIso
      ((coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm ((H).δ 0 e))))
      ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) (ULift.up ((H).δ 0 e))) :=
  vertexIsoOfEq (FunctorIso.app T z₁)
    (coherentKanRefinement_left_source_eq_original K L e)
    ((coherentKanRefinementLeft_right_source_eq_target K L e).trans
      (coherentKanRefinement_right_target_eq_original K L e))

/-- 始点成分は定値辺を除去した元の消去式の同じ指定成分を値まで保持する。 -/
lemma coherentKanRefinementSourceComparison_heq_reduced :
    HEq (vertexIsoOfEq (FunctorIso.app T z₀)
      (coherentKanRefinementRight_left_source_eq_target K L e) rfl)
      (coherentKanRefinementSourceComparison K L e) :=
  (vertexIsoOfEq_heq _ _ _).trans (vertexIsoOfEq_heq (FunctorIso.app T z₀)
    ((coherentKanRefinementRight_left_source_eq_target K L e).trans
      (coherentKanRefinement_left_target_eq_original K L e))
    (coherentKanRefinement_right_source_eq_original K L e)).symm

/-- 終点成分も元の消去式の同じ指定成分を値まで保持する。 -/
lemma coherentKanRefinementTargetComparison_heq_reduced :
    HEq (vertexIsoOfEq (FunctorIso.app T z₁) rfl
      (coherentKanRefinementLeft_right_source_eq_target K L e))
      (coherentKanRefinementTargetComparison K L e) :=
  (vertexIsoOfEq_heq _ _ _).trans (vertexIsoOfEq_heq (FunctorIso.app T z₁)
    (coherentKanRefinement_left_source_eq_original K L e)
    ((coherentKanRefinementLeft_right_source_eq_target K L e).trans
      (coherentKanRefinement_right_target_eq_original K L e))).symm

end SerrePositivity.InfinityCategories.F2
