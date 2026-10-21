module

public import SerrePositivity.InfinityCategories.F1.CocartesianSecondTriangleMiddleHom

/-!
概要：元の第二三角形の終域への混合 Hom は、同じ標準合成三角形の Hom と一致する。
方針：元の零成分の最後の零頂点評価に、元の終域輸送を後合成する。
規約：元の source の全 Hom と固定第二射を保持する。
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

/-- 元の第二三角形の始域から終域への Hom は、標準合成三角形の同じ Hom。 -/
lemma cocartesianSecondTriangleCutSimplex_zero_last
    (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : (stdSimplex.objEquiv a) i = 0) (hj : (stdSimplex.objEquiv a) j = 2) :
    (cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (cocartesianSecondTriangleCutSimplex_obj F G a s i)
        (cocartesianSecondTriangleCutSimplex_obj F G a s j)) =
      (cocartesianSecondTriangleCanonicalSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  apply simplicialHom_eq_of_normalized _ _
    (cocartesianSecondTriangleCutSimplex_obj F G a s i)
    (cocartesianSecondTriangleCutSimplex_obj F G a s j)
    (cocartesianSecondTriangleCutSimplex_obj_zero F G a s i hi)
    (cocartesianSecondTriangleCutSimplex_obj_last F G a s j hj)
    (cocartesianSecondTriangleCanonicalSimplex_obj_zero F G a s i hi)
    (cocartesianSecondTriangleCanonicalSimplex_obj_last F G a s j hj)
  have hL := cocartesianTransportHomCutSimplex_mixedHom_general_at F G
    (cocartesianSecondTriangleBaseSimplex a) s (cocartesianSecondTriangleTime a) i j hij
    (cocartesianSecondTriangleTime_zero a i hi) (cocartesianSecondTriangleTime_one a j 1 hj)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a i 0 hi)
    (cocartesianSecondTriangleBaseSimplex_obj_one a j hj) strictIntervalIndexArrow
  rw [cocartesianTransportDiagramMixedHom_post] at hL
  simp only [← Category.assoc] at hL
  rw [Category.assoc (pathCutLastZeroMap _ _ _) (SSet.yonedaEquiv.symm s),
    SSet.yonedaEquiv_symm_comp] at hL
  have hR := coherentCompositionNestedCutSimplex_zero_last_fixed
    (cocartesianTransportDiagramValue F (ULift.up 0))
    (cocartesianTransportDiagramValue G (ULift.up 0))
    (cocartesianTransportDiagramValue G (ULift.up 1))
    (show cocartesianTransportDiagramValue G (ULift.up 0) ⟶
      cocartesianTransportDiagramValue G (ULift.up 1) from G.val.map strictIntervalIndexArrow)
    ((quasicategoryCoreMap (strictDiagramMappingComponent F.val G.val (ULift.up 0))).app
      (Opposite.op ⦋n⦌) s)
    (cocartesianFirstTriangleTime a) (cocartesianSecondTriangleTime a)
    (cocartesianSecondTriangleTime_support a) i j
    (cocartesianSecondTriangleTime_zero a i hi) (cocartesianFirstTriangleTime_one a j hj)
  exact hL.trans hR.symm

end SerrePositivity.InfinityCategories
