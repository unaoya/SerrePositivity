module

public import SerrePositivity.InfinityCategories.F1.CoherentCosliceComparisonVertices
public import SerrePositivity.InfinityCategories.F1.PointedSpaceFiberVertices

/-!
概要：反転した一点 Hom から実際の pointed fiber への比較の零単体を計算する。
方針：左 coslice 比較が表す辺を元の通常の射へ戻し、Yoneda で指定点を回収する。
規約：標準 Kan 頂点への表示変更と元の係数の反転を保つ。
使われ方：相対恒等射の pointed 頂点を同じ合成輸送の一点 Hom 係数へ入れる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- pointed fiber の頂点の値は、同じ元の辺を標準頂点で読み直した射の Yoneda 評価。 -/
lemma pointedSpaceFiberVertexEquiv_edge (K : KanObject.{u})
    (s : (vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) _⦋0⦌) :
    pointedSpaceFiberVertexEquiv K s = SSet.yonedaEquiv
      (coherentNerveEdgeToHom (C := KanObject.{u}) (X := pointKanObject) (Y := K)
        ((cosliceFiberVertexToEdge s).ofEq
        (spaceInfinityVertex_eq_coherent pointKanObject) (spaceInfinityVertex_eq_coherent K))) := by
  rfl

/-- 実際の反転一点 Hom 比較の零単体は、元の点の Yoneda 評価を厳密に回収する。 -/
lemma pointedReverseKanFiberComparison_vertex (K : KanObject.{u}) (f : pointKanObject ⟶ K) :
    pointedSpaceFiberVertexEquiv K
      ((pointedReverseKanFiberComparison K).app (Opposite.op ⦋0⦌)
        (SSet.opObjEquiv.symm (ULift.up (SimplicialCategory.homEquiv' pointKanObject K f)))) =
      SSet.yonedaEquiv f := by
  rw [pointedSpaceFiberVertexEquiv_edge]
  have he : ((cosliceFiberVertexToEdge
      ((pointedReverseKanFiberComparison K).app (Opposite.op ⦋0⦌)
        (SSet.opObjEquiv.symm (ULift.up (SimplicialCategory.homEquiv' pointKanObject K f))))).ofEq
      (spaceInfinityVertex_eq_coherent pointKanObject) (spaceInfinityVertex_eq_coherent K)) =
      coherentNerveEdge f := by
    apply SSet.Edge.ext
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      ((pointedReverseKanFiberComparison K).app (Opposite.op ⦋0⦌)
        (SSet.opObjEquiv.symm
          (ULift.up (SimplicialCategory.homEquiv' pointKanObject K f)))).val.val) = _
    rw [pointedReverseKanFiberComparison_coordinates]
    change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      ((cosliceFiberVerticesIso (spaceInfinityVertex_eq_coherent pointKanObject).symm
        (spaceInfinityVertex_eq_coherent K).symm).hom.app (Opposite.op ⦋0⦌)
        ((HomotopyLimits.coherentCosliceFiberComparison pointKanObject K).app
          (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm
            (SimplicialCategory.homEquiv' pointKanObject K f))))).val.val) = _
    rw [cosliceFiberVerticesIso_app_val]
    change (cosliceFiberVertexToEdge
      ((HomotopyLimits.coherentCosliceFiberComparison pointKanObject K).app
        (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm
          (SimplicialCategory.homEquiv' pointKanObject K f))))).edge = _
    have h := congrArg SSet.Edge.edge
      (coherentCosliceFiberComparison_vertex_edge pointKanObject K
        (SimplicialCategory.homEquiv' pointKanObject K f))
    simpa only [Equiv.symm_apply_apply] using h
  rw [he, coherentNerveEdgeToHom_edge]

end SerrePositivity.InfinityCategories
