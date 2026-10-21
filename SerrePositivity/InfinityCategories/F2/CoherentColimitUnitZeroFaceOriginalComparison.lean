module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceOriginalSection
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitTetrahedronFirstEdges
public import SerrePositivity.InfinityCategories.F2.PointedPrismFamilyComparison

/-!
概要：元の第零面と第一辺で前合成した元の指定三角形を、全パラメータ固定で比較する。
方針：同じ可変初期値と底を厳密に回収し、同じ全延長空間の指定比較を使う。
規約：各点の同型に弱めない。使われ方：中央・最後の三単体の指定比較の三関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の第零面と元の指定三角形の前合成を、同じ全底・全初期値固定の空間で比較。 -/
def coherentColimitUnitZeroFaceOriginalComparison (k : Fin 3) (H : SSet.Homotopy F Q₀)
    (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
      SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
    {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
    (S : FunctorCompositionTriangle a b c)
    (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
      (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram) :=
  pointedPrismFamilyComparison (coherentColimitUnitPointedZeroFaceFamily B T k)
    (scaffoldFirstVertex_leftAnodyne 2)
    (coherentColimitUnitPointedZeroFaceLift B T k)
    (coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S)
    (coherentColimitUnitPointedZeroFaceLift_boundary B T k)
    (coherentColimitUnitPointedZeroFaceLift_projection B T k)
    (coherentColimitUnitZeroFaceOriginalTriangleLift_boundary B T k H he S)
    (coherentColimitUnitZeroFaceOriginalTriangleLift_projection B T k H he S hS)

/-- 中央の元の第零面を、元の第一辺で前合成した元の下単位三角形へ比較する。 -/
def coherentColimitUnitMiddleZeroFaceComparison :=
  coherentColimitUnitZeroFaceOriginalComparison B T 1 l
    (coherentColimitUnitTetrahedron_middle_firstEdge B T)
    (coherentColimitUnitLowerTriangle B r) (coherentColimitUnitTetrahedron_upper_last B T)

/-- 最後の元の第零面を、元の第一辺で前合成した元の上単位三角形へ比較する。 -/
def coherentColimitUnitLastZeroFaceComparison :=
  coherentColimitUnitZeroFaceOriginalComparison B T 2 l
    (coherentColimitUnitTetrahedron_last_firstEdge B T)
    (coherentColimitUnitUpperTriangle B r) (coherentColimitUnitTetrahedron_lower_last B T)

end SerrePositivity.InfinityCategories.F2
