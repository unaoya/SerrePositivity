module

public import SerrePositivity.InfinityCategories.F2.CoherentCompositionTetrahedron

/-!
概要：合成比較三単体の零面を元の三角形の最大化に同定する。
方針：対象写像は恒等、時刻は定値一となることを全頂点で計算する。
規約：新しい strict 化の選択を行わない。
使われ方：元の指定三角形と二辺の厳密合成の四面比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 零面の対象写像は恒等。 -/
lemma coherentCompositionTetrahedronObjects_face_zero :
    coherentCompositionTetrahedronObjects.{u}.comp
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap = OrderHom.id := by
  ext i
  rcases i with ⟨i⟩
  fin_cases i <;> rfl

/-- 零面の全頂点は時刻一。 -/
lemma coherentCompositionTetrahedronTime_face_zero :
    coherentCompositionTetrahedronTime.{u}.comp
      (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap = OrderHom.const _ 1 := by
  ext i
  rcases i with ⟨i⟩
  fin_cases i <;> rfl

/-- 零面は同じ元の三角形の最大 path 表示。 -/
lemma coherentCompositionTetrahedron_face_zero
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialNerve C).δ 0 (coherentCompositionTetrahedron s) =
      coherentSimplexMaximalization s := by
  change ((SimplicialThickening.functor
    (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap).comp SSet
    (coherentPathDeformationEnriched coherentCompositionTetrahedronObjects
      coherentCompositionTetrahedronTime)).comp SSet s = _
  rw [coherentPathDeformationEnriched_reindex,
    coherentCompositionTetrahedronObjects_face_zero,
    coherentCompositionTetrahedronTime_face_zero]
  rfl

end SerrePositivity.InfinityCategories.F2
