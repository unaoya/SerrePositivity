module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleThreeEdgeFormula
public import
  SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFixedFaceTriangleWitness

/-!
概要：元の単位三単体の全固定面の指定三角形比較を、同じ全実三辺の比較で表す。
方針：元の全空間射影と全係数を保つ三角形証拠へ、三辺による指定比較の式を適用する。
規約：全選択と実延長を保持。使われ方：固定面への右辺の指定自然性の適用。
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
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "C" => leftUnstraightening F ⊗ K
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F

local notation "W" => coherentColimitUnitPointedFixedFaceTriangleWitness B T k j hj S hS
local notation "V" => coherentTriangleOfFunctorTriangle S

/-- 元の同じ全単位面の指定三角形比較を、同じ全実持ち上げの三辺の指定比較で表す。 -/
lemma coherentColimitUnitPointedFixedFaceTriangle_heq_threeEdges :
    HEq (VertexIso.map (unstraighteningTriangleRelativeVertexIso F Q₁ Q₂
      (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
      (V).diagram (V).first (V).second (V).long)
      (relativeFunctorPre (leftUnstraighteningProjection Q₂)
        (leftUnstraighteningProjection F) (fst (leftUnstraightening F) K)))
      (functorHomotopySourceEndpointIso c p (fst (leftUnstraightening F) K) (rfl) (W).longWitness ≪≫
        ((functorHomotopySourceEndpointIso b p (W).middle (W).middle_projection
          (W).secondWitness).symm ≪≫ (W).firstInverseNativeComparison (rfl))) := by
  exact (W).specifiedTriangle_heq_threeEdges
    rfl

end SerrePositivity.InfinityCategories.F2
