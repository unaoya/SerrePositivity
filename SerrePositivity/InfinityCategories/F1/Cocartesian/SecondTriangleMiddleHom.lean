module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleObjects
public import SerrePositivity.InfinityCategories.F1.Cocartesian.MixedHomPostcomposition
public import SerrePositivity.InfinityCategories.F1.CoherentOrderHomNormalization

/-!
概要：元の第二三角形の最初の混合 Hom は、同じ標準合成三角形の Hom と一致する。
方針：同じ最後の零頂点で、元の零成分の Yoneda 族を評価する。
規約：固定成分の仮定なしに元の全 Hom の単体を保持する。
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

/-- 元の第二三角形の始域から中間対象への Hom は、標準合成三角形の同じ Hom。 -/
lemma cocartesianSecondTriangleCutSimplex_zero_middle
    (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : (stdSimplex.objEquiv a) i = 0) (hj : (stdSimplex.objEquiv a) j = 1) :
    (cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (cocartesianSecondTriangleCutSimplex_obj F G a s i)
        (cocartesianSecondTriangleCutSimplex_obj F G a s j)) =
      (cocartesianSecondTriangleCanonicalSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  apply simplicialHom_eq_of_normalized _ _
    (cocartesianSecondTriangleCutSimplex_obj F G a s i)
    (cocartesianSecondTriangleCutSimplex_obj F G a s j)
    (cocartesianSecondTriangleCutSimplex_obj_zero F G a s i hi)
    (cocartesianSecondTriangleCutSimplex_obj_middle F G a s j hj)
    (cocartesianSecondTriangleCanonicalSimplex_obj_zero F G a s i hi)
    (cocartesianSecondTriangleCanonicalSimplex_obj_middle F G a s j hj)
  have hL := cocartesianTransportHomCutSimplex_mixedHom_general_at F G
    (cocartesianSecondTriangleBaseSimplex a) s (cocartesianSecondTriangleTime a) i j hij
    (cocartesianSecondTriangleTime_zero a i hi) (cocartesianSecondTriangleTime_one a j 0 hj)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a i 0 hi)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a j 1 hj) (𝟙 (ULift.up (0 : Fin 2)))
  rw [cocartesianTransportDiagramMixedHom_base_id, SSet.yonedaEquiv_symm_comp] at hL
  exact hL.trans (coherentCompositionNestedCutSimplex_zero_middle _ _ _ _
    (cocartesianSecondTriangleTime_support a) i j
    (cocartesianSecondTriangleTime_zero a i hi)
    (cocartesianFirstTriangleTime_zero a j 1 hj)
    (cocartesianSecondTriangleTime_one a j 0 hj)).symm

end SerrePositivity.InfinityCategories
