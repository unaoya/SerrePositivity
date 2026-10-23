module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanRefinementEndpointComparisons
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.VertexIsoCompositionTransport

/-!
概要：元の精密化の反転側・右側の二区間像は同じ指定両端比較と整合する。
方針：二定値辺を除いた同じ消去式の四頂点と四同型を元の実辺へ表示変更する。
規約：元の F1 の二側比較と元の指定精密化の同じ類を保持する。
使われ方：反転精密化の作用と右 Hom の全係数の値を同じ区間輸送で照合する。
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

/-- 元の精密化の同じ左右区間像と指定された両端成分の同型の整合式。 -/
lemma coherentKanRefinement_original_square :
    coherentKanLeftRefinementIso K L e ≪≫ coherentKanRefinementSourceComparison K L e ≪≫
      coherentKanRightRefinementIso K L e = coherentKanRefinementTargetComparison K L e := by
  let a := edgewiseRefinementLeftImageIso FL e
  let b := vertexIsoOfEq (FunctorIso.app T z₀)
    (coherentKanRefinementRight_left_source_eq_target K L e) rfl
  let c := edgewiseRefinementRightImageIso FR e
  have hBC : HEq (b ≪≫ c)
      (coherentKanRefinementSourceComparison K L e ≪≫ coherentKanRightRefinementIso K L e) :=
    vertexIso_trans_heq_of_heq b c (coherentKanRefinementSourceComparison K L e)
      (coherentKanRightRefinementIso K L e)
      (coherentKanRefinement_left_target_eq_original K L e)
      (coherentKanRefinement_right_source_eq_original K L e)
      (coherentKanRefinement_right_target_eq_original K L e)
      (coherentKanRefinementSourceComparison_heq_reduced K L e)
      (coherentKanRefinementRight_right_iso_heq_original K L e)
  have hABC : HEq (a ≪≫ b ≪≫ c)
      (coherentKanLeftRefinementIso K L e ≪≫ coherentKanRefinementSourceComparison K L e ≪≫
        coherentKanRightRefinementIso K L e) :=
    vertexIso_trans_heq_of_heq a (b ≪≫ c) (coherentKanLeftRefinementIso K L e)
      (coherentKanRefinementSourceComparison K L e ≪≫ coherentKanRightRefinementIso K L e)
      (coherentKanRefinement_left_source_eq_original K L e)
      (coherentKanRefinement_left_target_eq_original K L e)
      (coherentKanRefinement_right_target_eq_original K L e)
      (coherentKanRefinementLeft_left_iso_heq_original K L e) hBC
  exact eq_of_heq (hABC.symm.trans
    ((heq_of_eq (coherentKanRefinement_reduced_square K L e)).trans
      (coherentKanRefinementTargetComparison_heq_reduced K L e)))

end SerrePositivity.InfinityCategories.F2
