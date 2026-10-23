module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanMorphismComparisonComponent
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanMorphismIntervalComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentKanLeftMorphismVertex
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.EdgewiseRefinementVertexProjections

/-!
概要：固定 Kan 射での指定左右区間比較は、元の実辺の区間頂点での恒等の類。
方針：退化した精密化の指定成分を同じ二側円柱へ戻し、その実定値性を使う。
規約：元の辺と指定比較を保持。使われ方：固定射の値比較の余分な区間因子を除く。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "H" => SimplicialCategory.sHom K L
local notation "e" => SimplicialObject.σ H 0 (functorVertex f)
local notation "z" => ULift.up (edgewiseRefinementVertex e)

/-- 固定射の指定左右比較は、その同じ退化 Hom 係数での元の二側比較の成分。 -/
lemma coherentKanMorphismIntervalComparison_heq_component :
    HEq (coherentKanMorphismIntervalComparison f) ((coherentKanTwoSidedIntervalIso K L).app z) := by
  have hc : (H).map (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0).op e = e := by
    rw [constantSimplexPullback_degenerate]
    change (H).σ 0 ((H).δ 1 e) = e
    rw [coherentKanMorphismDegenerate_source]
  have hs := (coherentKanRefinementSourceComparison_heq_reduced K L e).symm.trans
    (vertexIsoOfEq_heq _ _ _)
  have hm := functorIso_app_heq_of_vertex_eq (coherentKanTwoSidedIntervalIso K L)
    (congrArg (fun t => ULift.up (edgewiseRefinementVertex t)) hc)
  exact (vertexIsoOfEq_heq _ _ _).trans (hs.trans hm)

/-- 元の固定射の左右区間比較は、同じ実辺の区間頂点での恒等の値そのもの。 -/
lemma coherentKanMorphismIntervalComparison_heq_refl :
    HEq (coherentKanMorphismIntervalComparison f)
      (Iso.refl (SSet.HomotopyCategory.mk
        (intervalMappingVertexOfEdge (pointedRightMorphismEdge f)))) := by
  have hv : (((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight H) ≫
      coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌) z) =
      intervalMappingVertexOfEdge (pointedRightMorphismEdge f) := by
    change (coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
      (ULift.up ((edgewiseRight H).app (Opposite.op ⦋0⦌) (edgewiseRefinementVertex e))) = _
    rw [edgewiseRefinementVertex_right]
    have ht : (H).δ 0 e = functorVertex f := (SSet.Edge.id (functorVertex f)).tgt_eq
    rw [ht, coherentKanRightHomInterval_morphism]
  exact (coherentKanMorphismIntervalComparison_heq_component f).trans
    ((coherentKanTwoSidedIntervalIso_morphism_heq_refl f).trans
      (iso_refl_heq_of_eq (congrArg SSet.HomotopyCategory.mk hv)))

/-- 同じ恒等の値を、元の右 Hom の同じ頂点の表示でも保持する。 -/
lemma coherentKanMorphismIntervalComparison_heq_refl_right :
    HEq (coherentKanMorphismIntervalComparison f)
      (Iso.refl (SSet.HomotopyCategory.mk
        ((coherentKanRightHomInterval K L).app (Opposite.op ⦋0⦌)
          (ULift.up (functorVertex f))))) :=
  (coherentKanMorphismIntervalComparison_heq_refl f).trans
    (iso_refl_heq_of_eq (congrArg SSet.HomotopyCategory.mk
      (coherentKanRightHomInterval_morphism f).symm))

end SerrePositivity.InfinityCategories.F2
