module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SecondTriangleObjects
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionNestedPureHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CutPureHomEndpoint
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialHomConstantIdentity

/-!
概要：元の第二三角形の三つの同ラベル Hom を、元の対象の恒等に正規化する。
方針：同時刻の元の輸送射を、薄い底の同じ対象の恒等射へ戻す。
規約：元の全 Hom の単体を保持する。
使われ方：第二三角形の豊穣関手の一致の純粋部分。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
variable (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
variable (i j : Fin (n + 1)) (hij : i ≤ j)
include hij

/-- 元の第二三角形の零ラベル内の Hom は元の始域零成分の恒等。 -/
lemma cocartesianSecondTriangleCutSimplex_zeroHom
    (hi : (stdSimplex.objEquiv a) i = 0) (hj : (stdSimplex.objEquiv a) j = 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_zero F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_zero F G a s j hj)) =
      toUnit _ ≫ eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_zeroHom_at F G _ s _ i j hij
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_zero a i hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_zero a j hj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_zero a i 0 hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_zero a j 0 hj) (𝟙 (ULift.up (0 : Fin 2)))
  erw [F.val.map_id] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialHom_const_id _)

/-- 元の第二三角形の中間ラベル内の Hom は元の終域零成分の恒等。 -/
lemma cocartesianSecondTriangleCutSimplex_middleHom
    (hi : (stdSimplex.objEquiv a) i = 1) (hj : (stdSimplex.objEquiv a) j = 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_middle F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_middle F G a s j hj)) =
      toUnit _ ≫ eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_oneHom_at F G _ s _ i j hij
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a i 0 hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a j 0 hj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_zero a i 1 hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_zero a j 1 hj) (𝟙 (ULift.up (0 : Fin 2)))
  erw [G.val.map_id] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialHom_const_id _)

/-- 元の第二三角形の最終ラベル内の Hom は元の終域一成分の恒等。 -/
lemma cocartesianSecondTriangleCutSimplex_lastHom
    (hi : (stdSimplex.objEquiv a) i = 2) (hj : (stdSimplex.objEquiv a) j = 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_last F G a s i hi)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex_obj_last F G a s j hj)) =
      toUnit _ ≫ eId SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_oneHom_at F G _ s _ i j hij
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a i 1 hi) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a j 1 hj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_one a i hi)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_one a j hj) (𝟙 (ULift.up (1 : Fin 2)))
  erw [G.val.map_id] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialHom_const_id _)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
