module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitApexPointedVertexEndpoints
public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedFamilyEndpoint

/-!
概要：元の全三角形の同じ比較から、元の実中間・終 fiber 内の終点同型を回収する。
方針：同じ全比較を同じ実頂点で評価し、明示した元の係数作用と普遍輸送を結ぶ。
規約：二つの終点比較を独立に選び直さない。使われ方：元の指定境界への三辺の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "s" => coherentColimitApexTriangle B T
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "A" => spaceSimplexPointedCoefficients s

/-- 同じ全比較の中間頂点像。元の実中間 fiber の中で同じ第一輸送と比較する。 -/
def coherentColimitApexPointedMiddleEndpointIso :
    FunctorIso (coherentColimitApexMiddleCoefficientMap B T)
      (q ≫ coherentColimitRawFiberTransport B a) :=
  spaceSimplexPointedFamilyEndpointIso s (coherentColimitRawUniversalTrianglePrism B T q)
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T)
    (simplexPrismVertex 2 1 A) (coherentDiagramTotalCocone G).vertex
    (coherentColimitApexPointedMiddle_base B T)
    (coherentColimitApexMiddleCoefficientMap B T) (q ≫ coherentColimitRawFiberTransport B a)
    (coherentColimitApexMiddleCoefficientMap_ι B T).symm
    (coherentColimitApexPointedMiddle_endpoint B T)

/-- 同じ全比較の終頂点像。元の実終 fiber の中で同じ二辺の合成輸送と比較する。 -/
def coherentColimitApexPointedTargetEndpointIso :
    FunctorIso (coherentColimitApexTargetCoefficientMap B T)
      ((q ≫ coherentColimitRawFiberTransport B a) ≫ coherentColimitRawFiberTransport B b) :=
  spaceSimplexPointedFamilyEndpointIso s (coherentColimitRawUniversalTrianglePrism B T q)
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T)
    (simplexPrismVertex 2 2 A) (coherentDiagramTotalCocone J).vertex
    (coherentColimitApexPointedTarget_base B T)
    (coherentColimitApexTargetCoefficientMap B T)
    ((q ≫ coherentColimitRawFiberTransport B a) ≫ coherentColimitRawFiberTransport B b)
    (coherentColimitApexTargetCoefficientMap_ι B T).symm
    (coherentColimitApexPointedTarget_endpoint B T)

end SerrePositivity.InfinityCategories.F2
