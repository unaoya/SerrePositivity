module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalHomTriangles
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportHomCutSimplex

/-!
概要：元の第二三角形の時間と底の座標を、標準退化射で固定する。
方針：普遍二単体で座標を計算し、底の同型の全単体での対象作用を読む。
規約：元の正方形の下側三角形と同じ向きを使う。
使われ方：第二三角形の豊穣関手の等式を三つの頂点ラベルで検証する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 第二三角形の時間座標は、頂点列 0,1,1。 -/
lemma squareTriangle_one_time :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 ≫ fst (Δ[1] : SSet.{u}) Δ[1] = stdSimplex.σ (1 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 第二三角形の底座標は、頂点列 0,0,1。 -/
lemma squareTriangle_one_base :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 1 ≫ snd (Δ[1] : SSet.{u}) Δ[1] = stdSimplex.σ (0 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 元の第二三角形の任意の単体における、同じ底の射列。 -/
def cocartesianSecondTriangleBaseSimplex {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    (nerve (ULift.{u} (Fin 2))) _⦋n⦌ :=
  (((stdSimplex.σ (0 : Fin 2) : (Δ[2] : SSet.{u + 1}) ⟶ Δ[1]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso 1).hom).app (Opposite.op ⦋n⦌) a).down

/-- 同じ底の射列の対象は、元の二単体の頂点を 0,0,1 に写した値。 -/
lemma cocartesianSecondTriangleBaseSimplex_obj {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1)) :
    (cocartesianSecondTriangleBaseSimplex a).obj i =
      ULift.up ((SimplexCategory.σ (0 : Fin 2)).toOrderHom ((stdSimplex.objEquiv a) i)) := rfl

/-- 同じ第二三角形の時間ラベルは、元の二単体の頂点を 0,1,1 に写した値。 -/
def cocartesianSecondTriangleTime {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    Fin (n + 1) →o Fin 2 :=
  (stdSimplex.objEquiv ((stdSimplex.σ (1 : Fin 2)).app (Opposite.op ⦋n⦌) a)).toOrderHom

/-- 元の第二三角形の任意の単体で、同じ時間ラベルを計算する。 -/
lemma cocartesianSecondTriangleTime_apply {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1)) :
    cocartesianSecondTriangleTime a i =
      (SimplexCategory.σ (1 : Fin 2)).toOrderHom ((stdSimplex.objEquiv a) i) := rfl

/-- 元の第二三角形の同じ時間・底を使った、全次数の対角評価。 -/
def cocartesianSecondTriangleCutSimplex
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex F G (cocartesianSecondTriangleBaseSimplex a) s
    (cocartesianSecondTriangleTime a)

/-- 最初のラベルの時間は零。 -/
lemma cocartesianSecondTriangleTime_zero {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌)
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 0) :
    cocartesianSecondTriangleTime a i = 0 := by
  rw [cocartesianSecondTriangleTime_apply, hi]; rfl

/-- 後の二ラベルの時間は一。 -/
lemma cocartesianSecondTriangleTime_one {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌)
    (i : Fin (n + 1)) (k : Fin 2) (hi : (stdSimplex.objEquiv a) i = k.succ) :
    cocartesianSecondTriangleTime a i = 1 := by
  rw [cocartesianSecondTriangleTime_apply, hi]
  fin_cases k <;> rfl

/-- 最初の二ラベルの底対象は、元の始点。 -/
lemma cocartesianSecondTriangleBaseSimplex_obj_zero {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1)) (k : Fin 2)
    (hi : (stdSimplex.objEquiv a) i = k.castSucc) :
    (cocartesianSecondTriangleBaseSimplex a).obj i = ULift.up 0 := by
  rw [cocartesianSecondTriangleBaseSimplex_obj, hi]
  fin_cases k <;> rfl

/-- 最後のラベルの底対象は、元の終点。 -/
lemma cocartesianSecondTriangleBaseSimplex_obj_one {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1))
    (hi : (stdSimplex.objEquiv a) i = 2) :
    (cocartesianSecondTriangleBaseSimplex a).obj i = ULift.up 1 := by
  rw [cocartesianSecondTriangleBaseSimplex_obj, hi]; rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
