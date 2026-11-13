module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalTriangleFamilyComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleFaces
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.IntervalMappingOppositeComposition

/-!
概要：指定辺に定値な区間族と、定値関手の射を照合する。
方針：辺と区間頂点の往復、curry の自然性を使う。
規約：パラメータは任意の単体集合。使われ方：G8 の三角形の第二面。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：指定辺の区間頂点に定値な族は、同じ辺への第二射影。
方針：辺と区間頂点の往復と既存の展開式を使う。
規約：全パラメータを保持。使われ方：実三角形の第二面の照合。 -/
lemma intervalFamilyHomotopy_const_edge {A X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) :
    (intervalFamilyHomotopy (SSet.const (intervalMappingVertexOfEdge e) : A ⟶ _)).h =
      snd A (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge := by
  have he : intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge e) = e :=
    (intervalMappingEdgeVertexEquiv x y).symm_apply_apply e
  change (β_ A (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry _ = _
  rw [intervalMappingUncurry_const_vertex, he]
  rfl

/-- 概要：指定辺の定値区間族の類は、その辺の定値関手による像。
方針：curry の自然性で元の辺の全族を照合する。
規約：頂点ごとの等式に弱めない。使われ方：三面から標準後合成への接続。 -/
lemma intervalFamilyHom_const_edge {A X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) :
    intervalFamilyHom (SSet.const (intervalMappingVertexOfEdge e) : A ⟶ _) =
      constantFunctorHomMap A (SSet.Truncated.HomotopyCategory.homMk e) := by
  rw [constantFunctorHomMap_homMk]
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  change SSet.yonedaEquiv (curry (intervalFamilyHomotopy _).h) =
    (constantFunctorMap A X).app (Opposite.op ⦋1⦌) e.edge
  rw [intervalFamilyHomotopy_const_edge]
  have h : (constantFunctorMap A X).app (Opposite.op ⦋1⦌) e.edge =
      SSet.yonedaEquiv (SSet.yonedaEquiv.symm e.edge ≫ constantFunctorMap A X) := by
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [h, constantFunctorMap, ← curry_natural_left, whiskerLeft_snd]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
