module

public import SerrePositivity.InfinityCategories.F2.CoherentKanRefinementEndpointDependence

/-!
概要：同じ元の頂点での左右区間比較は、始点側・終点側の表示によらない。
方針：二つの定値引き戻しを同じ元の頂点の退化へ戻す。
規約：指定された二側比較の成分を保持。使われ方：固定 Kan 射での比較への統一。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 一方の精密化の終点と他方の始点が同じなら、指定比較の同じ成分を持つ。 -/
lemma coherentKanRefinementTargetComparison_heq_sourceComparison (K L : KanObject.{u})
    (e f : (SimplicialCategory.sHom K L) _⦋1⦌)
    (h : (SimplicialCategory.sHom K L).δ 0 e = (SimplicialCategory.sHom K L).δ 1 f) :
    HEq (coherentKanRefinementTargetComparison K L e)
      (coherentKanRefinementSourceComparison K L f) := by
  have hc : (SimplicialCategory.sHom K L).map
      (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1).op e =
      (SimplicialCategory.sHom K L).map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op f := by
    rw [constantSimplexPullback_degenerate, constantSimplexPullback_degenerate]
    change (SimplicialCategory.sHom K L).σ 0 ((SimplicialCategory.sHom K L).δ 0 e) =
      (SimplicialCategory.sHom K L).σ 0 ((SimplicialCategory.sHom K L).δ 1 f)
    rw [h]
  have he := (coherentKanRefinementTargetComparison_heq_reduced K L e).symm.trans
    (vertexIsoOfEq_heq _ _ _)
  have hf := (coherentKanRefinementSourceComparison_heq_reduced K L f).symm.trans
    (vertexIsoOfEq_heq _ _ _)
  have hm := functorIso_app_heq_of_vertex_eq (coherentKanTwoSidedIntervalIso K L)
    (congrArg (fun t => ULift.up (edgewiseRefinementVertex t)) hc)
  exact he.trans (hm.trans hf.symm)

end SerrePositivity.InfinityCategories.F2
