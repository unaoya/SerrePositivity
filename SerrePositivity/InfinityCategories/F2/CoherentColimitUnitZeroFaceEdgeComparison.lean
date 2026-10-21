module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceOriginalComparison
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceOriginalTarget
public import SerrePositivity.InfinityCategories.F2.PointedTriangleFamilyEdgeMap
public import SerrePositivity.InfinityCategories.F2.FunctorTrianglePointedLongWitness

/-!
概要：元の第零面の一つの全族比較を、元の同じ三辺へ制限する。
方針：元の指定比較を辺制限で写し、標的を元の指定三角形の辺の前合成へ厳密に揃える。
規約：辺ごとに比較を選び直さない。使われ方：六面の指定三関係の辺と終点の照合。
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
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k
local notation "w" => unstraighteningMappingTriangleLongWitness Q₀ Q₁ Q₂
  (SSet.const (coherentVertexOfHomotopy a)) (SSet.const (coherentVertexOfHomotopy b))
  (SSet.const (coherentVertexOfHomotopy c))
  (CoherentTransformationVertexTriangle.diagram (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.first (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.second (coherentTriangleOfFunctorTriangle S))
  (CoherentTransformationVertexTriangle.long (coherentTriangleOfFunctorTriangle S))

/-- 元の第零面の指定全族比較を、元の同じ辺へ写した指定比較。 -/
def coherentColimitUnitZeroFaceEdgeComparison (j : Fin 3) :=
  VertexIso.map (coherentColimitUnitZeroFaceOriginalComparison B T k H he S hS)
    (pointedTriangleFamilyEdgeMap D j)

/-- 三辺の比較の標的の実関手は、元の指定三角形の同じ辺の実第一辺による前合成。 -/
lemma coherentColimitUnitZeroFaceEdgeComparison_target (j : Fin 3) :
    (((pointedTriangleFamilyEdgeMap D j).app (Opposite.op ⦋0⦌)
      (pointedPrismFamilyFixedChoice_vertex D
        (coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S)
        (coherentColimitUnitZeroFaceOriginalTriangleLift_boundary B T k H he S)
        (coherentColimitUnitZeroFaceOriginalTriangleLift_projection B T k H he S hS))).val) =
    functorVertex ((α_ (Δ[1] : SSet.{u + 1}) (leftUnstraightening F) K).hom ≫
      (Δ[1] ◁ coherentColimitUnitPointedFirstEdgeEndpoint B T k H he) ≫
      (stdSimplex.δ j ▷ leftUnstraightening Q₀) ≫ functorTrianglePointedLift S) := by
  rw [pointedTriangleFamilyEdgeMap_vertex,
    coherentColimitUnitZeroFaceOriginalTriangleLift_edge B T k H he S j]

/-- 長辺の比較の標的は、元の指定比較に使った同じ全長辺証拠の実第一辺による制限。 -/
lemma coherentColimitUnitZeroFaceEdgeComparison_long_target :
    (((pointedTriangleFamilyEdgeMap D 1).app (Opposite.op ⦋0⦌)
      (pointedPrismFamilyFixedChoice_vertex D
        (coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S)
        (coherentColimitUnitZeroFaceOriginalTriangleLift_boundary B T k H he S)
        (coherentColimitUnitZeroFaceOriginalTriangleLift_projection B T k H he S hS))).val) =
    functorVertex ((α_ (Δ[1] : SSet.{u + 1}) (leftUnstraightening F) K).hom ≫
      prismParameterRestriction (lift (coherentColimitUnitPointedFirstEdgeEndpoint B T k H he)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) ≫ (w).prism) := by
  rw [coherentColimitUnitZeroFaceEdgeComparison_target B T k H he S hS 1]
  exact congrArg functorVertex (congrArg (fun z =>
    (α_ (Δ[1] : SSet.{u + 1}) (leftUnstraightening F) K).hom ≫ z)
      (functorTrianglePointedLift_long S (coherentColimitUnitPointedFirstEdgeEndpoint B T k H he)))

end SerrePositivity.InfinityCategories.F2
