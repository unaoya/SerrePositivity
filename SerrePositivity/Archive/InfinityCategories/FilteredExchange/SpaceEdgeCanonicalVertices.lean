module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedRightMorphismTransport

/-!
概要：元の Space 辺と、その元の Kan 射から作る辺の実一次単体・両端点を同定する。
方針：coherent 辺の厳密な復元式を二端点へ適用する。
規約：元の辺をホモトピーで置換しない。使われ方：普遍三角形の三辺の値比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の Space 辺の Kan 射から作る右 Hom の辺は、元の実一次単体を回収する。 -/
lemma pointedRightMorphismEdge_recover (e : SpaceInfinity.{u} _⦋1⦌) :
    (pointedRightMorphismEdge (coherentEdgeHom e)).edge = e := coherentEdge_recover e

/-- 元の Space 辺の始対象の標準頂点は、元の辺の実始点そのもの。 -/
lemma spaceEdge_source_vertex (e : SpaceInfinity.{u} _⦋1⦌) :
    spaceInfinityVertex (e.obj ⟨ULift.up 0⟩) = SpaceInfinity.δ 1 e := by
  have h := congrArg (SpaceInfinity.δ 1) (coherentEdge_recover e)
  exact (spaceInfinityVertex_eq_coherent _).trans
    ((coherentEdge_source (coherentEdgeHom e)).symm.trans h)

/-- 元の Space 辺の終対象の標準頂点は、元の辺の実終点そのもの。 -/
lemma spaceEdge_target_vertex (e : SpaceInfinity.{u} _⦋1⦌) :
    spaceInfinityVertex (e.obj ⟨ULift.up 1⟩) = SpaceInfinity.δ 0 e := by
  have h := congrArg (SpaceInfinity.δ 0) (coherentEdge_recover e)
  exact (spaceInfinityVertex_eq_coherent _).trans
    ((coherentEdge_target (coherentEdgeHom e)).symm.trans h)

/-- 元の指定始点から、同じ辺の始対象の標準頂点への実等式。 -/
lemma spaceEdge_source_to_object {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y) :
    x = spaceInfinityVertex (e.edge.obj ⟨ULift.up 0⟩) :=
  e.src_eq.symm.trans (spaceEdge_source_vertex e.edge).symm

/-- 元の指定終点から、同じ辺の終対象の標準頂点への実等式。 -/
lemma spaceEdge_target_to_object {x y : SpaceInfinity.{u} _⦋0⦌} (e : SSet.Edge x y) :
    y = spaceInfinityVertex (e.edge.obj ⟨ULift.up 1⟩) :=
  e.tgt_eq.symm.trans (spaceEdge_target_vertex e.edge).symm

end SerrePositivity.InfinityCategories.F2
