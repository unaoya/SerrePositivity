module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-!
概要：任意の図式間の同じ全ホモトピーを、変換空間の指定頂点として保持する。
方針：元の円柱の関手辺と区間写像空間の頂点との全単射を使う。
規約：元の全円柱への厳密な往復の式も保持する。
使われ方：前層値の密度自然変換を F2 の両端固定余錐実現へ入力する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K X : SSet.{u}} {f g : K ⟶ X} (H : SSet.Homotopy f g)

/-- 元の円柱の辺そのものを、同じ変換空間の頂点として読む。 -/
def homotopyTransformationVertex :
    (intervalMappingSpace (functorVertex f) (functorVertex g)) _⦋0⦌ :=
  intervalMappingVertexOfEdge (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy H))

/-- 指定頂点から回収した全円柱は、元の全円柱そのもの。 -/
lemma homotopyTransformationVertex_h :
    (simplicialHomotopyOfFunctorEdge
      (intervalMappingEdgeOfVertex (homotopyTransformationVertex H)).toTruncated).h = H.h := by
  have he := (intervalMappingEdgeVertexEquiv (functorVertex f) (functorVertex g)).symm_apply_apply
    (SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy H))
  have he' := congrArg SSet.Edge.edge he
  change (intervalMappingEdgeOfVertex (homotopyTransformationVertex H)).edge = _ at he'
  change uncurry (SSet.yonedaEquiv.symm
    (intervalMappingEdgeOfVertex (homotopyTransformationVertex H)).edge) = _
  rw [he']
  change uncurry (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry H.h))) = H.h
  rw [Equiv.symm_apply_apply, uncurry_curry]

end SerrePositivity.InfinityCategories.F2.Ind
