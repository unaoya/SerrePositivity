module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleThreeEdgeFormula
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceTriangleWitness

/-!
概要：元の単位三単体の全第零面の指定三角形比較を、同じ全実三辺の比較で表す。
方針：実第一辺の終点と全係数を保つ三角形証拠へ、三辺による指定比較の式を適用する。
規約：全選択と実延長を保持。使われ方：元の第零面への右辺の指定自然性の適用。
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
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "C" => leftUnstraightening F ⊗ K
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "f" => coherentColimitUnitPointedFirstEdgeEndpoint B T k H he
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k

local notation "W" => coherentColimitUnitZeroFaceTriangleWitness B T k H he S hS
local notation "V" => coherentTriangleOfFunctorTriangle S

/-- 元の同じ全単位面の指定三角形比較を、同じ全実持ち上げの三辺の指定比較で表す。 -/
lemma coherentColimitUnitZeroFaceTriangle_heq_threeEdges :
    HEq (VertexIso.map (unstraighteningTriangleRelativeVertexIso Q₀ Q₁ Q₂
      (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
      (V).diagram (V).first (V).second (V).long)
      (relativeFunctorPre (leftUnstraighteningProjection Q₂)
        (leftUnstraighteningProjection Q₀) f))
      (functorHomotopySourceEndpointIso c p f
        (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k H he) (W).longWitness ≪≫
        ((functorHomotopySourceEndpointIso b p (W).middle (W).middle_projection
          (W).secondWitness).symm ≪≫ (W).firstInverseNativeComparison
            (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k H he))) := by
  exact (W).specifiedTriangle_heq_threeEdges
    (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k H he)

end SerrePositivity.InfinityCategories.F2
