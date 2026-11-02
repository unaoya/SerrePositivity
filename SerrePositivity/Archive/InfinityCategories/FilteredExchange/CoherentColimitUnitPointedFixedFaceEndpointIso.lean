module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFixedFaceEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionEndpointWitness

/-!
概要：元の固定始点の二面の実終点と、元の二作用を合成した射を同じ終点比較で結ぶ。
方針：元の二つの全持ち上げ・全初期値・実終点を一つの共通証拠型へ束ねる。
規約：全パラメータと既存の指定終点比較を保持。使われ方：三関係の native 終点表示。
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
local notation "D" => coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS
local notation "b₂" => ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫
  PointedTransportPrismFamily.diagram (coherentColimitUnitPointedFixedFaceFamily B T k j hj S hS)
local notation "i₂" => (scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ K
local notation "j₂" => simplexPrismVertex 2 2 (leftUnstraightening F) ▷ K

/-- 元の固定始点の二面と元の指定三角形を、同じ全底・全初期値・終点の証拠で保持。 -/
def coherentColimitUnitPointedFixedFaceEndpointWitness (original : Bool) :
    RelativeExtensionEndpointWitness pointedSpaceProjection b₂ i₂ (D).boundary j₂ Q₂
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) := by
  cases original
  · exact ⟨coherentColimitUnitPointedFixedFaceLift B T k j,
      coherentColimitUnitPointedFixedFaceLift_projection B T k j hj S hS,
      coherentColimitUnitPointedFixedFaceLift_boundary B T k j hj S hS,
      coherentColimitUnitPointedFixedFaceEndpoint B T k j hj S hS,
      coherentColimitUnitPointedFixedFaceEndpoint_projection B T k j hj S hS,
      coherentColimitUnitPointedFixedFaceEndpoint_pointed B T k j hj S hS⟩
  · exact ⟨coherentColimitUnitPointedFixedFaceOriginalLift B T k S,
      coherentColimitUnitPointedFixedFaceOriginalLift_projection B T k j hj S hS,
      coherentColimitUnitPointedFixedFaceOriginalLift_boundary B T k j hj S hS,
      coherentColimitUnitPointedFixedFaceOriginalTarget B T k S,
      coherentColimitUnitPointedFixedFaceOriginalTarget_projection B T k S,
      coherentColimitUnitPointedFixedFaceOriginalLift_target B T k S⟩

/-- 元の固定始点の二面の実終点を、元の二作用の native 合成へ結ぶ同じ指定終点比較。 -/
def coherentColimitUnitPointedFixedFaceEndpointIso :
    VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection Q₂)
        (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
        (coherentColimitUnitPointedFixedFaceEndpoint B T k j hj S hS)
        (coherentColimitUnitPointedFixedFaceEndpoint_projection B T k j hj S hS))
      (relativeFunctorVertex (leftUnstraighteningProjection Q₂)
        (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
        (coherentColimitUnitPointedFixedFaceOriginalTarget B T k S)
        (coherentColimitUnitPointedFixedFaceOriginalTarget_projection B T k S)) :=
  (coherentColimitUnitPointedFixedFaceEndpointWitness B T k j hj S hS false).iso
    (coherentColimitUnitPointedFixedFaceEndpointWitness B T k j hj S hS true)
    (leftAnodyneExtensions_whiskerRight _
      (simplexPrismFirstVertex_leftAnodyne 2 (leftUnstraightening F)) K)
    (D).projection (coherentColimitUnitPointedFixedFaceBase_endpoint B T k j hj S hS)

end SerrePositivity.InfinityCategories.F2
