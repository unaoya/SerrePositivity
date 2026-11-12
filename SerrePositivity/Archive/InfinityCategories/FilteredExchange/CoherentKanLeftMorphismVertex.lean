module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentKanLeftHomInterval
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SpaceTriangleHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CosliceComparisonVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedRightMorphismTransport

/-!
概要：元の固定 Kan 射の左区間頂点は、同じ元の coherent 辺の区間頂点である。
方針：元の coslice 頂点の実辺を回収し、標準両端への表示変更だけを行う。
規約：元の射と実辺を保持。使われ方：固定射での左右比較と元の長辺との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の反転 Hom の左区間の零成分は、同じ元の Kan 射の実辺の区間頂点。 -/
lemma coherentKanLeftHomInterval_morphism {K L : KanObject.{u}} (f : K ⟶ L) :
    (coherentKanLeftHomInterval K L).app (Opposite.op ⦋0⦌)
      (ULift.up (SSet.opObjEquiv.symm (functorVertex f))) =
    intervalMappingVertexOfEdge (pointedRightMorphismEdge f) := by
  change (intervalMappingPostOfEq (𝟙 SpaceInfinity.{u})
    (coherentNerveVertex K) (coherentNerveVertex L)
    (spaceInfinityVertex_eq_coherent K).symm (spaceInfinityVertex_eq_coherent L).symm).app _
      ((cosliceFiberToIntervalMappingSpace (coherentNerveVertex K) (coherentNerveVertex L)).app _
        ((coherentCosliceFiberComparison K L).app _
          (ULift.up (SSet.opObjEquiv.symm (functorVertex f))))) = _
  rw [← kanHom_vertex K L f, cosliceFiberToIntervalMappingSpace_vertex,
    coherentCosliceFiberComparison_vertex_edge, Equiv.symm_apply_apply,
    intervalMappingPostOfEq_vertex]
  rfl

end SerrePositivity.InfinityCategories.F2
