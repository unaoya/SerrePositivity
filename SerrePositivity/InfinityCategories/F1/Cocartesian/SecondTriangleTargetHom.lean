module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleMiddleHom
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CutPureHomEndpoint

/-!
概要：元の第二三角形の終域側の Hom は、標準合成三角形の同じ固定第二射。
方針：同時刻一の元の輸送射と、標準合成の定値第二パラメーターを比較する。
規約：元の終域図式の輸送射を保持する。
使われ方：第二三角形全体の豊穣関手の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の第二三角形の中間対象から終域への Hom は、標準三角形の同じ Hom。 -/
lemma cocartesianSecondTriangleCutSimplex_middle_last
    (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : (stdSimplex.objEquiv a) i = 1) (hj : (stdSimplex.objEquiv a) j = 2) :
    (cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (cocartesianSecondTriangleCutSimplex_obj F G a s i)
        (cocartesianSecondTriangleCutSimplex_obj F G a s j)) =
      (cocartesianSecondTriangleCanonicalSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  apply simplicialHom_eq_of_normalized _ _
    (cocartesianSecondTriangleCutSimplex_obj F G a s i)
    (cocartesianSecondTriangleCutSimplex_obj F G a s j)
    (cocartesianSecondTriangleCutSimplex_obj_middle F G a s i hi)
    (cocartesianSecondTriangleCutSimplex_obj_last F G a s j hj)
    (cocartesianSecondTriangleCanonicalSimplex_obj_middle F G a s i hi)
    (cocartesianSecondTriangleCanonicalSimplex_obj_last F G a s j hj)
  have hL := cocartesianTransportHomCutSimplex_oneHom_at F G
    (cocartesianSecondTriangleBaseSimplex a) s (cocartesianSecondTriangleTime a) i j hij
    (cocartesianSecondTriangleTime_one a i 0 hi) (cocartesianSecondTriangleTime_one a j 1 hj)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a i 1 hi)
    (cocartesianSecondTriangleBaseSimplex_obj_one a j hj) strictIntervalIndexArrow
  have hR := coherentCompositionNestedCutSimplex_middle_last_fixed
    (cocartesianTransportDiagramValue F (ULift.up 0))
    (cocartesianTransportDiagramValue G (ULift.up 0))
    (cocartesianTransportDiagramValue G (ULift.up 1))
    (show cocartesianTransportDiagramValue G (ULift.up 0) ⟶
      cocartesianTransportDiagramValue G (ULift.up 1) from G.val.map strictIntervalIndexArrow)
    ((quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))).app
      (Opposite.op ⦋n⦌) s)
    (cocartesianFirstTriangleTime a) (cocartesianSecondTriangleTime a) i j
    (cocartesianFirstTriangleTime_zero a i 1 hi) (cocartesianSecondTriangleTime_one a i 0 hi)
    (cocartesianFirstTriangleTime_one a j hj)
  exact hL.trans hR.symm

end SerrePositivity.InfinityCategories
