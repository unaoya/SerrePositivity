module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceEndpoint
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionEndpointWitness

/-!
概要：元の第零面の実終点と、実第一辺に元の二作用を合成した射を同じ終点比較で結ぶ。
方針：元の二つの全持ち上げ・可変初期値・実終点を一つの共通証拠型へ束ねる。
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
local notation "b₂" => ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫
  PointedTransportPrismFamily.diagram (coherentColimitUnitPointedZeroFaceFamily B T k)
local notation "i₂" => (scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ K
local notation "j₂" => simplexPrismVertex 2 2 (leftUnstraightening F) ▷ K

/-- 元の第零面と前合成した元の指定三角形を、同じ全底・全初期値・終点の証拠で保持。 -/
def coherentColimitUnitZeroFaceEndpointWitness (original : Bool) :
    RelativeExtensionEndpointWitness pointedSpaceProjection b₂ i₂ (D).boundary j₂ Q₂
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) := by
  cases original
  · exact ⟨coherentColimitUnitPointedZeroFaceLift B T k,
      coherentColimitUnitPointedZeroFaceLift_projection B T k,
      coherentColimitUnitPointedZeroFaceLift_boundary B T k,
      coherentColimitUnitZeroFaceEndpoint B T k H he S hS,
      coherentColimitUnitZeroFaceEndpoint_projection B T k H he S hS,
      coherentColimitUnitZeroFaceEndpoint_pointed B T k H he S hS⟩
  · exact ⟨coherentColimitUnitZeroFaceOriginalTriangleLift B T k H he S,
      coherentColimitUnitZeroFaceOriginalTriangleLift_projection B T k H he S hS,
      coherentColimitUnitZeroFaceOriginalTriangleLift_boundary B T k H he S,
      coherentColimitUnitZeroFaceOriginalTargetMap B T k H he S,
      coherentColimitUnitZeroFaceOriginalTargetMap_projection B T k H he S,
      coherentColimitUnitZeroFaceOriginalTriangleLift_target B T k H he S⟩

/-- 元の第零面の実終点を、元の二作用の native 合成へ結ぶ同じ指定終点比較。 -/
def coherentColimitUnitZeroFaceEndpointIso :
    VertexIso
      (relativeFunctorVertex (leftUnstraighteningProjection Q₂)
        (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
        (coherentColimitUnitZeroFaceEndpoint B T k H he S hS)
        (coherentColimitUnitZeroFaceEndpoint_projection B T k H he S hS))
      (relativeFunctorVertex (leftUnstraighteningProjection Q₂)
        (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
        (coherentColimitUnitZeroFaceOriginalTargetMap B T k H he S)
        (coherentColimitUnitZeroFaceOriginalTargetMap_projection B T k H he S)) :=
  (coherentColimitUnitZeroFaceEndpointWitness B T k H he S hS false).iso
    (coherentColimitUnitZeroFaceEndpointWitness B T k H he S hS true)
    (leftAnodyneExtensions_whiskerRight _
      (simplexPrismFirstVertex_leftAnodyne 2 (leftUnstraightening F)) K)
    (D).projection (coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS)

end SerrePositivity.InfinityCategories.F2
