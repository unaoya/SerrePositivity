module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SecondTriangleCanonical

/-!
概要：元の第二三角形の三対象を、標準合成三角形と同じ対象へ正規化する。
方針：時間と底の座標の計算を元の対角評価へ適用する。
規約：元の全 Hom の単体を変えない。
使われ方：第二三角形全体の豊穣関手の外延性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
variable (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)

/-- 元の第二三角形の最初の対象は、元の始域図式の零成分。 -/
lemma cocartesianSecondTriangleCutSimplex_obj_zero
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s).obj ⟨ULift.up i⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 0) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_zero F G _ s _ i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_zero a i hi)).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_zero a i 0 hi))

/-- 元の第二三角形の中間対象は、元の終域図式の零成分。 -/
lemma cocartesianSecondTriangleCutSimplex_obj_middle
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 1) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s).obj ⟨ULift.up i⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 0) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_one F G _ s _ i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a i 0 hi)).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_zero a i 1 hi))

/-- 元の第二三角形の最終対象は、元の終域図式の一成分。 -/
lemma cocartesianSecondTriangleCutSimplex_obj_last
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s).obj ⟨ULift.up i⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_one F G _ s _ i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleTime_one a i 1 hi)).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleBaseSimplex_obj_one a i hi))

/-- 元の第二三角形と標準合成三角形は、全次数で同じ対象を持つ。 -/
lemma cocartesianSecondTriangleCutSimplex_obj
    (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCutSimplex F G a s).obj ⟨ULift.up i⟩ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex F G a s).obj ⟨ULift.up i⟩ := by
  generalize hi : (stdSimplex.objEquiv a) i = k
  fin_cases k
  · exact (cocartesianSecondTriangleCutSimplex_obj_zero F G a s i hi).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_zero F G a s i hi).symm
  · exact (cocartesianSecondTriangleCutSimplex_obj_middle F G a s i hi).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_middle F G a s i hi).symm
  · exact (cocartesianSecondTriangleCutSimplex_obj_last F G a s i hi).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSecondTriangleCanonicalSimplex_obj_last F G a s i hi).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
