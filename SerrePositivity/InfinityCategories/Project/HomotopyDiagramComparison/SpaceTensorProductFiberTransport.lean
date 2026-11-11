module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpaceTensorProductProjection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointedTensorFiberTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PairedFiberTransportVertices

/-!
概要：空間の二項積関手の二射影に沿う普遍 fiber 輸送の対は同値。
方針：標準頂点で元の fst・snd の辺を回収し、任意の頂点を標準頂点で表示する。
規約：元の coherent な射影辺を使う。使われ方：点ごとの積図式の fiber 判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan

/-- 空間の積関手の元の二射影辺に沿う普遍 fiber 輸送の対。 -/
def spaceTensorProductFiberTransport (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProduct.app (Opposite.op ⦋0⦌) (s, t)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t :=
  lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductFstHomotopy (s, t)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductSndHomotopy (s, t)))

/-- 標準頂点で、同じ二射影辺の fiber 輸送の対は同値。 -/
lemma spaceTensorProductFiberTransport_standard_isQCatEquivalence (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (spaceTensorProductFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex L)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductFstHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex L)
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductSndHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex L)
  have he : e.ofEq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProduct_vertex K L) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ K from fst K.obj L.obj) := by
    apply SSet.Edge.ext
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductFstHomotopy_component K L
  have hf : f.ofEq (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProduct_vertex K L) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensorLeft K).obj L ⟶ L from snd K.obj L.obj) := by
    apply SSet.Edge.ext
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProductSndHomotopy_component K L
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pairedFiberTransport_isQCatEquivalence_iff_of_vertices _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.spaceTensorProduct_vertex K L) rfl rfl e f).mpr
  rw [he, hf]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointedTensorFiberTransport_isQCatEquivalence K L

/-- 任意の二頂点で、積関手の指定二射影による普遍 fiber 輸送の対は同値。 -/
lemma spaceTensorProductFiberTransport_isQCatEquivalence
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (spaceTensorProductFiberTransport s t) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object s, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object t]
  exact spaceTensorProductFiberTransport_standard_isQCatEquivalence _ _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
