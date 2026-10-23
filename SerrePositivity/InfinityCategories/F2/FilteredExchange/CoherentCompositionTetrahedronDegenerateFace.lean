module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionTetrahedronDegeneratePath

/-!
概要：合成比較三単体の最後の面は元の最初の辺の退化。
方針：対象写像 (0,0,1) と path の像の計算を使う。
規約：元の辺を厳密に保持し、恒等辺を新たに選ばない。
使われ方：四面の比較の恒等因子を同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 最後の面の対象写像は最初の辺への退化の対象写像。 -/
lemma coherentCompositionTetrahedronLastObjects_eq :
    coherentCompositionTetrahedronLastObjects.{u} =
      (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap.comp
        (SimplexCategory.σ (0 : Fin 2)).toOrderHom.uliftMap := by
  ext i
  rcases i with ⟨i⟩
  fin_cases i <;> rfl

/-- 最後の面は元の最初の辺の始点を繰り返す退化二単体。 -/
lemma coherentCompositionTetrahedron_face_three
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (SimplicialNerve C).δ 3 (coherentCompositionTetrahedron s) =
      (SimplicialNerve C).σ 0 ((SimplicialNerve C).δ 2 s) := by
  change ((SimplicialThickening.functor
    (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap).comp SSet
    (coherentPathDeformationEnriched coherentCompositionTetrahedronObjects
      coherentCompositionTetrahedronTime)).comp SSet s = _
  rw [coherentPathDeformationEnriched_reindex]
  change (coherentPathDeformationEnriched coherentCompositionTetrahedronLastObjects
    _).comp SSet s = _
  rw [coherentCompositionTetrahedronLastObjects_enriched,
    coherentCompositionTetrahedronLastObjects_eq, SimplicialThickening.functor_comp]
  rfl

end SerrePositivity.InfinityCategories.F2
