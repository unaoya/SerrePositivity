module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitDiagonal
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentFunctorTriangle

/-!
概要：単位正方形を、元の対角円柱を共有する実際の二つの合成三角形に分ける。
方針：標準二三角形へ制限し、元の四辺と同じ対角を厳密に回収する。
規約：合成の存在から三角形を選び直さない。使われ方：native 写像の単位整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の変換と標的の native 単位を結ぶ、元の全正方形の上側三角形。 -/
def coherentColimitUnitUpperTriangle : FunctorCompositionTriangle H
    (coconeTransformationHomotopy (coherentDiagramTotalCocone G))
    (coherentColimitUnitDiagonal B H) where
  diagram := squareTriangle 0 ≫ coherentColimitUnitSquare B H
  face_zero := by
    rw [← Category.assoc, triangleSquare_upper_top, coherentColimitUnitSquare_top]
  face_one := by
    rw [← Category.assoc, squareTriangle_diagonal, coherentColimitUnitDiagonal_curry]
  face_two := by
    rw [← Category.assoc, triangleSquare_upper_left, coherentColimitUnitSquare_source]

/-- 始域の native 単位と余極限の指定辺を結ぶ、元の全正方形の下側三角形。 -/
def coherentColimitUnitLowerTriangle : FunctorCompositionTriangle
    (coconeTransformationHomotopy (coherentDiagramTotalCocone F))
    (simplicialHomotopyOfFunctorEdge (coherentColimitConstantEdge B H))
    (coherentColimitUnitDiagonal B H) where
  diagram := squareTriangle 1 ≫ coherentColimitUnitSquare B H
  face_zero := by
    rw [← Category.assoc, triangleSquare_lower_right, coherentColimitUnitSquare_target]
    change _ = curry (uncurry (SSet.yonedaEquiv.symm (coherentColimitConstantEdge B H).edge))
    rw [curry_uncurry]
    exact (coherentColimitConstantEdge_curry B H).symm
  face_one := by
    rw [← Category.assoc, squareTriangle_diagonal, coherentColimitUnitDiagonal_curry]
  face_two := by
    rw [← Category.assoc, triangleSquare_lower_bottom, coherentColimitUnitSquare_bottom]

end SerrePositivity.InfinityCategories.F2
