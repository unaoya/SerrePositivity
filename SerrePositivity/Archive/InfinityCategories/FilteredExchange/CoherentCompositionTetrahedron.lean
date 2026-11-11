module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTriangleDeformationTime
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexDeformation

/-!
概要：元の三角形と最大 path による合成を同じ三単体の面に置く。
方針：頂点 (0,0,1,2) と時刻 (0,1,1,1) の path 変形を使う。
規約：元の二単体の指定された精密化を保持する。
使われ方：長辺と二辺合成の全族の比較の四面整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 合成比較三単体の対象写像 (0,0,1,2)。 -/
def coherentCompositionTetrahedronObjects : ULift.{u} (Fin 4) →o ULift.{u} (Fin 3) :=
  (SimplexCategory.σ (0 : Fin 3)).toOrderHom.uliftMap

/-- 合成比較三単体の時刻 (0,1,1,1)。 -/
def coherentCompositionTetrahedronTime : ULift.{u} (Fin 4) →o Fin 2 :=
  coherentTriangleDeformationTime.{u}.comp
    (SimplexCategory.σ (2 : Fin 3)).toOrderHom.uliftMap

/-- 元の三角形と厳密合成を結ぶ、選択を含まない三単体。 -/
def coherentCompositionTetrahedron {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) : (SimplicialNerve C) _⦋3⦌ :=
  (coherentPathDeformationEnriched coherentCompositionTetrahedronObjects
    coherentCompositionTetrahedronTime).comp SSet s

/-- 元の三角形が載る面で対象写像は恒等。 -/
lemma coherentCompositionTetrahedronObjects_face_one :
    coherentCompositionTetrahedronObjects.comp
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap = OrderHom.id := by
  ext i
  rcases i with ⟨i⟩
  fin_cases i <;> rfl

/-- 元の三角形が載る面の時刻は (0,1,1)。 -/
lemma coherentCompositionTetrahedronTime_face_one :
    coherentCompositionTetrahedronTime.comp
      (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap =
        coherentTriangleDeformationTime := by
  ext i
  rcases i with ⟨i⟩
  fin_cases i <;> rfl

/-- 第一面は精密化を含む元の coherent 三角形そのもの。 -/
lemma coherentCompositionTetrahedron_face_one
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialNerve C).δ 1 (coherentCompositionTetrahedron s) = s := by
  change ((SimplicialThickening.functor
    (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap).comp SSet
    (coherentPathDeformationEnriched coherentCompositionTetrahedronObjects
      coherentCompositionTetrahedronTime)).comp SSet s = s
  rw [coherentPathDeformationEnriched_reindex,
    coherentCompositionTetrahedronObjects_face_one,
    coherentCompositionTetrahedronTime_face_one,
    coherentTriangleDeformationTime_enriched]
  rfl

end SerrePositivity.InfinityCategories.F2
