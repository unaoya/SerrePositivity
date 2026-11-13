module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdges
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpaceTriangleHomotopy

/-!
概要：𝒮 の三辺が指定射である三角形の可換性。
方針：三頂点と三辺の射データを揃えて元の三角形のホモトピーを移す。
規約：長辺から二辺の合成への向きを保持する。
使われ方：引き戻し錐の二つの native な三角形の可換性の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：三辺を指定射と同定した 𝒮 の三角形から指定ホモトピーを作る。
方針：三つの対象と射を元の辺から読み戻し、ホモトピーを輸送する。
規約：元の二単体を変更せず、別のホモトピーの代表を選ばない。
使われ方：native な錐の三角形を二脚と図式の射のホモトピーにする。 -/
def spaceInfinityTriangleHomotopy_of_faces {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋2⦌)
    (h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g).edge)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 1 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h).edge) : SSet.Homotopy h (f ≫ g) := by
  have hx : s.obj ⟨ULift.up 0⟩ = X :=
    congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 0⟩) h₂
  have hy : s.obj ⟨ULift.up 1⟩ = Y :=
    congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₂
  have hz : s.obj ⟨ULift.up 2⟩ = Z :=
    congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋1⦌ ↦ t.obj ⟨ULift.up 1⟩) h₀
  subst X
  subst Y
  subst Z
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2 s) = f := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData h₂
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0 s) = g := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData h₀
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow] at h
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentEdgeHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 1 s) = h := by
    have he := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData h₁
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow] at he
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  have e := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityTriangleHomotopy s
  rw [hf, hg, hh] at e
  exact e

end SerrePositivity.InfinityCategories.Project.FilteredExchange
