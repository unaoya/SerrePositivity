module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FirstTriangleCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalSourceComposition

/-!
概要：元の第一三角形と指定合成三角形の対象を、全次数で一致させる。
方針：時間・底の二つの退化座標を三頂点のラベルで計算する。
規約：固定成分の頂点と元の輸送射から定めた同じ通常の三角形を使う。
使われ方：第一三角形の豊穣関手の等式の対象部分。

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

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)

/-- 固定成分と元の輸送射からなる、指定合成三角形の通常の二射列。 -/
def cocartesianFirstTriangleSourceDiagram : ComposableArrows _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} 2 :=
  ComposableArrows.mk₂
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 0) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1) from F.val.map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.strictIntervalIndexArrow)
    ((SimplicialCategory.homEquiv' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up 1))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1))).symm b.down)

/-- 任意次数の元の第一三角形と指定三角形は、同じ頂点ラベルで同じ対象を持つ。 -/
lemma cocartesianFirstTriangleCutSimplex_obj {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleCutSimplex F G a s).obj ⟨ULift.up i⟩ =
      (cocartesianFirstTriangleSourceDiagram F G b).obj ((stdSimplex.objEquiv a) i) := by
  generalize hi : (stdSimplex.objEquiv a) i = k
  fin_cases k
  · have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime a i = 0 := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_apply, hi]; rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_zero F G _ s _ i ht).trans (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleBaseSimplex_obj, hi]; rfl)
  · have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime a i = 0 := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_apply, hi]; rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_zero F G _ s _ i ht).trans (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleBaseSimplex_obj, hi]; rfl)
  · have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime a i = 1 := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleTime_apply, hi]; rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_one F G _ s _ i ht).trans (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianFirstTriangleBaseSimplex_obj, hi]; rfl)

/-- 指定射列を Hom の宇宙に合わせた通常の順序図式として読む。 -/
def cocartesianFirstTriangleSourceOrderDiagram : ULift.{u} (Fin 3) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 3) →o Fin 3).toFunctor ⋙
    cocartesianFirstTriangleSourceDiagram F G b

/-- 任意の二単体パラメーターで指定三角形を制限した、同じ strict な coherent 図式。 -/
def cocartesianFirstTriangleCanonicalSimplex {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram ((stdSimplex.objEquiv a).toOrderHom.uliftMap.toFunctor ⋙
    cocartesianFirstTriangleSourceOrderDiagram F G b)

/-- 指定図式の制限は、元の指定合成三角形の同じ単体制限。 -/
lemma cocartesianFirstTriangleCanonicalSimplex_eq_map {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) :
    cocartesianFirstTriangleCanonicalSimplex F G b a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.map (stdSimplex.objEquiv a).op
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalSourceCompStruct F G b).simplex := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ =
    (SimplicialThickening.functor (stdSimplex.objEquiv a).toOrderHom.uliftMap).comp SSet
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_precomp _ _).symm

/-- 最初の二ラベルの指定図式の対象は、元の始域図式の同じ対象。 -/
lemma cocartesianFirstTriangleCanonicalSimplex_obj_zero {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1)) (k : Fin 2)
    (hi : (stdSimplex.objEquiv a) i = k.castSucc) :
    (cocartesianFirstTriangleCanonicalSimplex F G b a).obj ⟨ULift.up i⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (ULift.up k) := by
  change (cocartesianFirstTriangleSourceDiagram F G b).obj ((stdSimplex.objEquiv a) i) = _
  rw [hi]
  fin_cases k <;> rfl

/-- 最終ラベルの指定図式の対象は、元の終域図式の終点。 -/
lemma cocartesianFirstTriangleCanonicalSimplex_obj_one {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (i : Fin (n + 1))
    (hi : (stdSimplex.objEquiv a) i = 2) :
    (cocartesianFirstTriangleCanonicalSimplex F G b a).obj ⟨ULift.up i⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G (ULift.up 1) := by
  change (cocartesianFirstTriangleSourceDiagram F G b).obj ((stdSimplex.objEquiv a) i) = _
  rw [hi]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
