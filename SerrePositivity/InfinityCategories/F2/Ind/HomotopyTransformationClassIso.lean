module

public import SerrePositivity.InfinityCategories.F2.Ind.HomotopyTransformationVertex
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyClasses

/-!
概要：元の全変換の h Fun の類の一致を、同じ変換空間内の頂点同型へ戻す。
方針：元の辺を右写像空間へ戻し、π₀ と h Fun の同値と区間模型への比較を使う。
規約：端点と指定変換を保持。使われ方：単位の類を保つ相対 join 実現の係数比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の全変換の h Fun の類が等しければ、同じ変換空間内の元の指定頂点は同型。 -/
def homotopyTransformationClassIso {K X : SSet.{u}} [Quasicategory X]
    {f g : K ⟶ X} (H H' : SSet.Homotopy f g)
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H')) :
    VertexIso (homotopyTransformationVertex H) (homotopyTransformationVertex H') := by
  let a := (pinchedHomVertexEquiv (functorVertex f) (functorVertex g)).symm
    (functorEdgeOfSimplicialHomotopy H)
  let b := (pinchedHomVertexEquiv (functorVertex f) (functorVertex g)).symm
    (functorEdgeOfSimplicialHomotopy H')
  have hp : SSet.π₀.mk a = SSet.π₀.mk b := by
    apply (pinchedHomPiZeroEquiv (functorVertex f) (functorVertex g)).injective
    change SSet.Truncated.HomotopyCategory.homMk
      (pinchedHomVertexEquiv (functorVertex f) (functorVertex g) a) =
      SSet.Truncated.HomotopyCategory.homMk
        (pinchedHomVertexEquiv (functorVertex f) (functorVertex g) b)
    simpa only [a, b, Equiv.apply_symm_apply] using h
  let e := Classical.choice (nonempty_vertexIso_of_piZero_eq hp)
  have he := e.map (pinchedHomToIntervalMappingSpace (functorVertex f) (functorVertex g))
  rw [pinchedHomToIntervalMappingSpace_vertex, pinchedHomToIntervalMappingSpace_vertex] at he
  simpa only [a, b, Equiv.apply_symm_apply, homotopyTransformationVertex,
    SSet.Edge.ofTruncated] using he

end SerrePositivity.InfinityCategories.F2.Ind
