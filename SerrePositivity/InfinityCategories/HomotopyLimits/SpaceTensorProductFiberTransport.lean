module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTensorProductProjection
public import SerrePositivity.InfinityCategories.HomotopyLimits.PointedTensorFiberTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.PairedFiberTransportVertices

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration kanTensor_isKan

/-- 空間の積関手の元の二射影辺に沿う普遍 fiber 輸送の対。 -/
def spaceTensorProductFiberTransport (s t : SpaceInfinity.{u} _⦋0⦌) :
    vertexFiber pointedSpaceProjection (spaceTensorProduct.app (Opposite.op ⦋0⦌) (s, t)) ⟶
      vertexFiber pointedSpaceProjection s ⊗ vertexFiber pointedSpaceProjection t :=
  lift
    (edgeTransport pointedSpaceProjection
      (simplicialHomotopyVertexEdge spaceTensorProductFstHomotopy (s, t)))
    (edgeTransport pointedSpaceProjection
      (simplicialHomotopyVertexEdge spaceTensorProductSndHomotopy (s, t)))

/-- 標準頂点で、同じ二射影辺の fiber 輸送の対は同値。 -/
lemma spaceTensorProductFiberTransport_standard_isQCatEquivalence (K L : KanObject.{u}) :
    IsQCatEquivalence
      (spaceTensorProductFiberTransport (coherentNerveVertex K) (coherentNerveVertex L)) := by
  let e := simplicialHomotopyVertexEdge spaceTensorProductFstHomotopy
    (coherentNerveVertex K, coherentNerveVertex L)
  let f := simplicialHomotopyVertexEdge spaceTensorProductSndHomotopy
    (coherentNerveVertex K, coherentNerveVertex L)
  have he : e.ofEq (spaceTensorProduct_vertex K L) rfl =
      coherentNerveEdge (show (kanTensorLeft K).obj L ⟶ K from fst K.obj L.obj) := by
    apply SSet.Edge.ext
    exact spaceTensorProductFstHomotopy_component K L
  have hf : f.ofEq (spaceTensorProduct_vertex K L) rfl =
      coherentNerveEdge (show (kanTensorLeft K).obj L ⟶ L from snd K.obj L.obj) := by
    apply SSet.Edge.ext
    exact spaceTensorProductSndHomotopy_component K L
  apply (pairedFiberTransport_isQCatEquivalence_iff_of_vertices pointedSpaceProjection
    (spaceTensorProduct_vertex K L) rfl rfl e f).mpr
  rw [he, hf]
  exact pointedTensorFiberTransport_isQCatEquivalence K L

/-- 任意の二頂点で、積関手の指定二射影による普遍 fiber 輸送の対は同値。 -/
lemma spaceTensorProductFiberTransport_isQCatEquivalence
    (s t : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (spaceTensorProductFiberTransport s t) := by
  rw [← coherentNerveVertex_object s, ← coherentNerveVertex_object t]
  exact spaceTensorProductFiberTransport_standard_isQCatEquivalence _ _

end SerrePositivity.InfinityCategories.HomotopyLimits
