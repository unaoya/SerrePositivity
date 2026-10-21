module

public import SerrePositivity.InfinityCategories.F1.EquivalencePathFamilyEdge

/-!
概要：可逆 path の族から、同じ関手空間の辺の類を順方向の射とする関手同型を作る。
方針：元の path の頂点条件で同じ辺の可逆性を判定する。
規約：別の同型代表を選び直さず、元の一単体の類を保持する。
使われ方：補正成分の同型と元の自然性のホモトピー圏での照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の全 path を表す同じ関手空間の辺は可逆。 -/
lemma equivalencePathFamilyEdge_isInvertible {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y) :
    IsInvertibleEdge (equivalencePathFamilyEdge L).toTruncated := by
  apply (isInvertibleEdge_iff_evaluateFunctorAt (equivalencePathFamilyEdge L).toTruncated).mpr
  intro x
  have hv := fullSubcomplexOnVertices_vertex (L.app (Opposite.op ⦋0⦌) x)
  change IsInvertibleEdge (edgeOfSimplex (intervalFunctorVertexEdge
    ((L ≫ equivalencePathι Y).app (Opposite.op ⦋0⦌) x))) at hv
  exact (isInvertibleEdge_congr
    (intervalFamily_vertex_edge (L ≫ equivalencePathι Y) x).symm).mpr hv

/-- 元の全 path の族の同じ辺の類を順方向の射とする関手同型。 -/
def equivalencePathFamilyIso {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y) :
    FunctorIso (L ≫ equivalencePathEndpoint Y 0) (L ≫ equivalencePathEndpoint Y 1) := by
  letI := equivalencePathFamilyEdge_isInvertible L
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (equivalencePathFamilyEdge L).toTruncated)

/-- 同じ関手同型の順方向の射は、元の全 path を表す一単体の類そのもの。 -/
lemma equivalencePathFamilyIso_hom {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y) :
    (equivalencePathFamilyIso L).hom =
      SSet.Truncated.HomotopyCategory.homMk (equivalencePathFamilyEdge L).toTruncated := rfl

end SerrePositivity.InfinityCategories
