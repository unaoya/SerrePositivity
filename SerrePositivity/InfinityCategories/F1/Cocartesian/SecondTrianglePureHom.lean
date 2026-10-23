module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SecondTriangleObjects
public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionNestedPureHom
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CutPureHomEndpoint
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplicialHomConstantIdentity

/-!
概要：元の第二三角形の三つの同ラベル Hom を、元の対象の恒等に正規化する。
方針：同時刻の元の輸送射を、薄い底の同じ対象の恒等射へ戻す。
規約：元の全 Hom の単体を保持する。
使われ方：第二三角形の豊穣関手の一致の純粋部分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
variable (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
variable (i j : Fin (n + 1)) (hij : i ≤ j)
include hij

/-- 元の第二三角形の零ラベル内の Hom は元の始域零成分の恒等。 -/
lemma cocartesianSecondTriangleCutSimplex_zeroHom
    (hi : (stdSimplex.objEquiv a) i = 0) (hj : (stdSimplex.objEquiv a) j = 0) :
    (cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (cocartesianSecondTriangleCutSimplex_obj_zero F G a s i hi)
        (cocartesianSecondTriangleCutSimplex_obj_zero F G a s j hj)) =
      toUnit _ ≫ eId SSet (cocartesianTransportDiagramValue F (ULift.up 0)) := by
  have h := cocartesianTransportHomCutSimplex_zeroHom_at F G _ s _ i j hij
    (cocartesianSecondTriangleTime_zero a i hi) (cocartesianSecondTriangleTime_zero a j hj)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a i 0 hi)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a j 0 hj) (𝟙 (ULift.up (0 : Fin 2)))
  erw [F.val.map_id] at h
  exact h.trans (simplicialHom_const_id _)

/-- 元の第二三角形の中間ラベル内の Hom は元の終域零成分の恒等。 -/
lemma cocartesianSecondTriangleCutSimplex_middleHom
    (hi : (stdSimplex.objEquiv a) i = 1) (hj : (stdSimplex.objEquiv a) j = 1) :
    (cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (cocartesianSecondTriangleCutSimplex_obj_middle F G a s i hi)
        (cocartesianSecondTriangleCutSimplex_obj_middle F G a s j hj)) =
      toUnit _ ≫ eId SSet (cocartesianTransportDiagramValue G (ULift.up 0)) := by
  have h := cocartesianTransportHomCutSimplex_oneHom_at F G _ s _ i j hij
    (cocartesianSecondTriangleTime_one a i 0 hi) (cocartesianSecondTriangleTime_one a j 0 hj)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a i 1 hi)
    (cocartesianSecondTriangleBaseSimplex_obj_zero a j 1 hj) (𝟙 (ULift.up (0 : Fin 2)))
  erw [G.val.map_id] at h
  exact h.trans (simplicialHom_const_id _)

/-- 元の第二三角形の最終ラベル内の Hom は元の終域一成分の恒等。 -/
lemma cocartesianSecondTriangleCutSimplex_lastHom
    (hi : (stdSimplex.objEquiv a) i = 2) (hj : (stdSimplex.objEquiv a) j = 2) :
    (cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (cocartesianSecondTriangleCutSimplex_obj_last F G a s i hi)
        (cocartesianSecondTriangleCutSimplex_obj_last F G a s j hj)) =
      toUnit _ ≫ eId SSet (cocartesianTransportDiagramValue G (ULift.up 1)) := by
  have h := cocartesianTransportHomCutSimplex_oneHom_at F G _ s _ i j hij
    (cocartesianSecondTriangleTime_one a i 1 hi) (cocartesianSecondTriangleTime_one a j 1 hj)
    (cocartesianSecondTriangleBaseSimplex_obj_one a i hi)
    (cocartesianSecondTriangleBaseSimplex_obj_one a j hj) (𝟙 (ULift.up (1 : Fin 2)))
  erw [G.val.map_id] at h
  exact h.trans (simplicialHom_const_id _)

end SerrePositivity.InfinityCategories
