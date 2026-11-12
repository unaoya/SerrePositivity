module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionTetrahedronRefinementPaths
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentPathHom

/-!
概要：合成比較三単体の第二面は元の指定精密化を保持する。
方針：両端の path の等式と包含射の一意性で辺を同定する。
規約：ホモトピー類だけでなく実際の Hom の一単体を同定する。
使われ方：元の長辺と二辺合成の比較への四面整合の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

local notation "A" => coherentCompositionTetrahedronRefinementObjects
local notation "t" => coherentCompositionTetrahedronRefinementTime

/-- 第二面の精密化の nerve の辺は元の精密化の辺と厳密に一致。 -/
lemma coherentCompositionTetrahedron_refinement_chain :
    (nerveMap (coherentPathDeformationFunctor A t
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2))).app
        (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ coherentTriangleRefinement) =
      ComposableArrows.mk₁ coherentTriangleRefinement := by
  refine ComposableArrows.ext₁ coherentCompositionTetrahedron_refinement_source
    coherentCompositionTetrahedron_refinement_target ?_
  exact coherentPathHom_ext _ _

/-- 第二面を元の Hom へ写すと元の指定精密化の実際の一単体に等しい。 -/
lemma coherentCompositionTetrahedron_face_two_homotopy
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    coherentTriangleHomotopy ((SimplicialNerve C).δ 2
      (coherentCompositionTetrahedron s)) = coherentTriangleHomotopy s := by
  change (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app (Opposite.op ⦋1⦌)
    ((nerveMap ((SimplicialThickening.functorMap
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) ⋙
      coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
        coherentCompositionTetrahedronTime _ _)).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ coherentTriangleRefinement)) = _
  have hchain : (nerveMap ((SimplicialThickening.functorMap
      (SimplexCategory.δ (2 : Fin 4)).toOrderHom.uliftMap
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) ⋙
      coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
        coherentCompositionTetrahedronTime _ _)).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ coherentTriangleRefinement) =
        ComposableArrows.mk₁ coherentTriangleRefinement := by
    refine ComposableArrows.ext₁ ?_ ?_ ?_
    · exact (coherentPathDeformation_reindex _ _ _ _).symm.trans
        coherentCompositionTetrahedron_refinement_source
    · exact (coherentPathDeformation_reindex _ _ _ _).symm.trans
        coherentCompositionTetrahedron_refinement_target
    · exact coherentPathHom_ext _ _
  rw [hchain]
  rfl

end SerrePositivity.InfinityCategories.F2
