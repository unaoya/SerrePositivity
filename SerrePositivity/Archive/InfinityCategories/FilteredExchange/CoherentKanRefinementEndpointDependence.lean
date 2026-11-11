module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanRefinementEndpointComparisons
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPre

/-!
概要：左右区間の指定両端比較は、精密化の元の両端だけで決まる。
方針：共通解像の定値引き戻しを元の端点の退化へ戻し、指定成分を照合する。
規約：同型の値を保持。使われ方：三角形比較の両端成分を同じ元の射へ統一する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ端点を持つ二辺の、その端点への定値引き戻しは厳密に等しい。 -/
lemma constantSimplexPullback_eq_of_face {X : SSet.{u}} (e f : X _⦋1⦌) (j : Fin 2)
    (h : X.δ j.rev e = X.δ j.rev f) :
    X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op e =
      X.map (SimplexCategory.const ⦋1⦌ ⦋1⦌ j).op f := by
  rw [constantSimplexPullback_degenerate, constantSimplexPullback_degenerate, h]

variable (K L : KanObject.{u}) (e f : (SimplicialCategory.sHom K L) _⦋1⦌)
local notation "H" => SimplicialCategory.sHom K L

/-- 元の精密化の始点が同じなら、同じ指定左右区間比較の始点成分も値まで一致する。 -/
lemma coherentKanRefinementSourceComparison_heq_of_source
    (h : (H).δ 1 e = (H).δ 1 f) :
    HEq (coherentKanRefinementSourceComparison K L e)
      (coherentKanRefinementSourceComparison K L f) := by
  have he := (coherentKanRefinementSourceComparison_heq_reduced K L e).symm.trans
    (vertexIsoOfEq_heq _ _ _)
  have hf := (coherentKanRefinementSourceComparison_heq_reduced K L f).symm.trans
    (vertexIsoOfEq_heq _ _ _)
  have hm := functorIso_app_heq_of_vertex_eq (coherentKanTwoSidedIntervalIso K L)
    (congrArg (fun t => ULift.up (edgewiseRefinementVertex t))
      (constantSimplexPullback_eq_of_face e f 0 h))
  exact he.trans (hm.trans hf.symm)

/-- 元の精密化の終点が同じなら、同じ指定左右区間比較の終点成分も値まで一致する。 -/
lemma coherentKanRefinementTargetComparison_heq_of_target
    (h : (H).δ 0 e = (H).δ 0 f) :
    HEq (coherentKanRefinementTargetComparison K L e)
      (coherentKanRefinementTargetComparison K L f) := by
  have he := (coherentKanRefinementTargetComparison_heq_reduced K L e).symm.trans
    (vertexIsoOfEq_heq _ _ _)
  have hf := (coherentKanRefinementTargetComparison_heq_reduced K L f).symm.trans
    (vertexIsoOfEq_heq _ _ _)
  have hm := functorIso_app_heq_of_vertex_eq (coherentKanTwoSidedIntervalIso K L)
    (congrArg (fun t => ULift.up (edgewiseRefinementVertex t))
      (constantSimplexPullback_eq_of_face e f 1 h))
  exact he.trans (hm.trans hf.symm)

end SerrePositivity.InfinityCategories.F2
