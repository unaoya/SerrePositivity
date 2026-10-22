module

public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementConstantIsos
public import SerrePositivity.InfinityCategories.F2.VertexIsoSpanRemoveConstant

/-!
概要：元の左右区間比較の消去式から二定値辺を除き、元の精密化の二 path を保つ。
方針：実退化辺から得た端点等式と恒等同型の値を同じ元の消去式へ代入する。
規約：元の F1 の指定成分は端点の表示変更だけを受ける。
使われ方：元の反転精密化と右精密化を全係数輸送の同じ値で照合する。
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
local notation "z₀" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) e))
local notation "z₁" => ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map H (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) e))

/-- 二定値辺の類を除去した同じ元の左右精密化と指定両端成分の整合式。 -/
lemma coherentKanRefinement_reduced_square :
    edgewiseRefinementLeftImageIso FL e ≪≫
        vertexIsoOfEq (FunctorIso.app T z₀)
          (coherentKanRefinementRight_left_source_eq_target K L e) rfl ≪≫
        edgewiseRefinementRightImageIso FR e =
      vertexIsoOfEq (FunctorIso.app T z₁) rfl
        (coherentKanRefinementLeft_right_source_eq_target K L e) :=
  vertexIso_span_remove_constant
    (edgewiseRefinementRightImageIso FL e) (edgewiseRefinementLeftImageIso FR e)
    (edgewiseRefinementLeftImageIso FL e) (edgewiseRefinementRightImageIso FR e)
    (FunctorIso.app T z₀) (FunctorIso.app T z₁)
    (coherentKanRefinementRight_left_source_eq_target K L e)
    (coherentKanRefinementLeft_right_source_eq_target K L e)
    (coherentKanRefinementRight_left_iso_heq_refl K L e)
    (coherentKanRefinementLeft_right_iso_heq_refl K L e)
    (coherentKanRefinement_common_component_cancel K L e)

end SerrePositivity.InfinityCategories.F2
