module
public import SerrePositivity.KST.SConstruction.DGKFixedInterface
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomIntervalVertices

/-!
概要：厳密 dg 入力間の native Hom 頂点を、同じ固定端点の coherent nerve 辺として読む。
方針：元の関手と native 頂点の実同値を逆に使い、通常射の標準辺を取る。
規約：native Hom の一単体と、入力 nerve の一単体を混同しない。
使われ方：懸垂の native 商作用の頂点から edgeIso の比較辺を取り出す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded KST.SConstruction
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (A B : PerfDGInput.{u, v} R)

/-- native Hom の頂点が表す、同じ二つの dg 入力を端点とする標準辺。 -/
def dgNativeMappingVertexEdge
    (p : (dgFunctorNativeMappingSpace R A B).obj (Opposite.op ⦋0⦌)) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((perfDGInputVertexEquiv R A B).symm (ULift.up p))

/-- 元の厳密入力射の native 頂点は、同じ射の標準辺を厳密に回収する。 -/
lemma dgNativeMappingVertexEdge_vertex (f : A ⟶ B) :
    dgNativeMappingVertexEdge R A B (dgFunctorNativeMappingVertex R A B f.down) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((perfDGInputVertexEquiv R A B).symm
    (perfDGInputVertexEquiv R A B f)) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f
  rw [Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
