module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointPaths
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentTriangleHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentPathHom

/-!
概要：零面の実円柱の終点の豊穣辺は元の指定精密化そのもの。
方針：二端点の実 path の等式と精密化の一意性で nerve の一単体を同定する。
規約：指定 path を別の代表に置き換えない。
使われ方：全族比較の終点像を元の指定 path の作用へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- prefix 円柱の実終点の辺は元の三角形の指定 Hom 辺に厳密に等しい。 -/
lemma coherentCompositionEndpoint_refinement
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    coherentTriangleHomotopy
      (coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
        (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2))) =
      coherentTriangleHomotopy s := by
  have hchain : (nerveMap
      (coherentPrefixPathDeformationFunctor coherentCompositionEndpointObjects
        coherentCompositionEndpointTime (ULift.up 0) (ULift.up 2) ⋙
      coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
        coherentCompositionTetrahedronTime _ _)).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ coherentTriangleRefinement) =
      ComposableArrows.mk₁ coherentTriangleRefinement := by
    refine ComposableArrows.ext₁ coherentCompositionEndpoint_path_source
      coherentCompositionEndpoint_path_target ?_
    exact coherentPathHom_ext _ _
  change (s.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩).app (Opposite.op ⦋1⦌)
    ((nerveMap (coherentPrefixPathDeformationFunctor coherentCompositionEndpointObjects
      coherentCompositionEndpointTime (ULift.up 0) (ULift.up 2) ⋙
      coherentPathDeformationFunctor coherentCompositionTetrahedronObjects
        coherentCompositionTetrahedronTime _ _)).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ coherentTriangleRefinement)) = _
  rw [hchain]
  rfl

end SerrePositivity.InfinityCategories.F2
