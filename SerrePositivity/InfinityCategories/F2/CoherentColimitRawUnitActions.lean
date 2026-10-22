module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTriangles
public import SerrePositivity.InfinityCategories.F2.FunctorHomotopyRelativePost

/-!
概要：元の単位正方形の raw 全空間上の下面・上面の実合成射を保持する。
方針：元の二辺の unstraightening 実作用をそのまま合成する。
規約：単位頂点・指定辺を保持。使われ方：最初辺の比較と一点輸送の交換式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : SSet.Homotopy F G)

/-- 元の余錐単位と元の定値余極限辺を合成した、値射影前の同じ実下面作用。 -/
def coherentColimitRawLowerCompositeAction :=
  (leftUnstraighteningMappingVertexMap F (SSet.const (coherentDiagramTotalCocone F).vertex)
    (coherentVertexOfHomotopy (coconeTransformationHomotopy (coherentDiagramTotalCocone F)))).val ≫
  (leftUnstraighteningMappingVertexMap
    (SSet.const (coherentDiagramTotalCocone F).vertex)
    (SSet.const (coherentDiagramTotalCocone G).vertex)
    (coherentVertexOfHomotopy
      (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B a)))).val

/-- 元の変換と元の標的余錐単位を合成した、値射影前の同じ実上面作用。 -/
def coherentColimitRawUpperCompositeAction :=
  (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
  (leftUnstraighteningMappingVertexMap G (SSet.const (coherentDiagramTotalCocone G).vertex)
    (coherentVertexOfHomotopy (coconeTransformationHomotopy (coherentDiagramTotalCocone G)))).val

end SerrePositivity.InfinityCategories.F2
