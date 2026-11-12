module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalHomTriangles
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportHomCutSimplex

/-!
概要：元の第一三角形の時間と底の座標を、標準退化射で固定する。
方針：普遍二単体で座標を計算し、底の同型の全単体での対象作用を読む。
規約：元の正方形の上側三角形と同じ向きを使う。
使われ方：第一三角形の豊穣関手の等式を三つの頂点ラベルで検証する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 第一三角形の時間座標は、頂点列 0,0,1。 -/
lemma squareTriangle_zero_time :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 ≫ fst (Δ[1] : SSet.{u}) Δ[1] = stdSimplex.σ (0 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 第一三角形の底座標は、頂点列 0,1,1。 -/
lemma squareTriangle_zero_base :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u} 0 ≫ snd (Δ[1] : SSet.{u}) Δ[1] = stdSimplex.σ (1 : Fin 2) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 元の第一三角形の任意の単体における、同じ底の射列。 -/
def cocartesianFirstTriangleBaseSimplex {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    (nerve (ULift.{u} (Fin 2))) _⦋n⦌ :=
  (((stdSimplex.σ (1 : Fin 2) : (Δ[2] : SSet.{u + 1}) ⟶ Δ[1]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localKanDiagramBaseIso 1).hom).app (Opposite.op ⦋n⦌) a).down

/-- 同じ底の射列の対象は、元の二単体の頂点を 0,1,1 に写した値。 -/
lemma cocartesianFirstTriangleBaseSimplex_obj {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1)) :
    (cocartesianFirstTriangleBaseSimplex a).obj i =
      ULift.up ((SimplexCategory.σ (1 : Fin 2)).toOrderHom ((stdSimplex.objEquiv a) i)) := rfl

/-- 同じ第一三角形の時間ラベルは、元の二単体の頂点を 0,0,1 に写した値。 -/
def cocartesianFirstTriangleTime {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    Fin (n + 1) →o Fin 2 :=
  (stdSimplex.objEquiv ((stdSimplex.σ (0 : Fin 2)).app (Opposite.op ⦋n⦌) a)).toOrderHom

/-- 元の第一三角形の任意の単体で、同じ時間ラベルを計算する。 -/
lemma cocartesianFirstTriangleTime_apply {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1)) :
    cocartesianFirstTriangleTime a i =
      (SimplexCategory.σ (0 : Fin 2)).toOrderHom ((stdSimplex.objEquiv a) i) := rfl

/-- 元の第一三角形の同じ時間・底を使った、全次数の対角評価。 -/
def cocartesianFirstTriangleCutSimplex
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2))) {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex F G (cocartesianFirstTriangleBaseSimplex a) s
    (cocartesianFirstTriangleTime a)

/-- 最初の二ラベルの時間は零。 -/
lemma cocartesianFirstTriangleTime_zero {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌)
    (i : Fin (n + 1)) (k : Fin 2) (hi : (stdSimplex.objEquiv a) i = k.castSucc) :
    cocartesianFirstTriangleTime a i = 0 := by
  rw [cocartesianFirstTriangleTime_apply, hi]
  fin_cases k <;> rfl

/-- 最初の二ラベルの底対象は、同じラベルの底対象。 -/
lemma cocartesianFirstTriangleBaseSimplex_obj_zero {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1)) (k : Fin 2)
    (hi : (stdSimplex.objEquiv a) i = k.castSucc) :
    (cocartesianFirstTriangleBaseSimplex a).obj i = ULift.up k := by
  rw [cocartesianFirstTriangleBaseSimplex_obj, hi]
  fin_cases k <;> rfl

/-- 最終ラベルの時間は一。 -/
lemma cocartesianFirstTriangleTime_one {n : ℕ} (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌)
    (i : Fin (n + 1)) (hi : (stdSimplex.objEquiv a) i = 2) :
    cocartesianFirstTriangleTime a i = 1 := by
  rw [cocartesianFirstTriangleTime_apply, hi]; rfl

/-- 最終ラベルの底対象は、元の底の終点。 -/
lemma cocartesianFirstTriangleBaseSimplex_obj_one {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1))
    (hi : (stdSimplex.objEquiv a) i = 2) :
    (cocartesianFirstTriangleBaseSimplex a).obj i = ULift.up 1 := by
  rw [cocartesianFirstTriangleBaseSimplex_obj, hi]; rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
