module


public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.BoundaryEdgeLifting

/-!
概要：単射への全 RLP を持つ射の同じ fiber の二頂点を、射影に垂直な辺で結ぶ。
方針：同じ像の恒等辺を、指定両端と一次元境界で持ち上げる。
規約：元・底の Kan 性は不要。使われ方：全 BF 写像空間での相対単位比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

structure RelativeMappingEdge {E B : SSet.{u}} (p : E ⟶ B) (x y : E _⦋0⦌) where
  edge : E.Edge x y
  over : p.app (Opposite.op ⦋1⦌) edge.edge =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (p.app (Opposite.op ⦋0⦌) x) 1

def relativeMappingEdge {E B : SSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) (x y : E _⦋0⦌)
    (h : p.app (Opposite.op ⦋0⦌) x = p.app (Opposite.op ⦋0⦌) y) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.RelativeMappingEdge p x y := by
  apply Classical.choice
  let : HasLiftingProperty (boundary 1).ι p := hp _ inferInstance
  let e := ((SSet.Edge.id (p.app (Opposite.op ⦋0⦌) x)).ofEq rfl h).toTruncated
  obtain ⟨l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_edge_lift_of_boundary_one p x y e
  refine ⟨⟨SSet.Edge.ofTruncated (X := E) l, ?_⟩⟩
  exact (congrArg Truncated.Edge.edge hl).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).symm

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
