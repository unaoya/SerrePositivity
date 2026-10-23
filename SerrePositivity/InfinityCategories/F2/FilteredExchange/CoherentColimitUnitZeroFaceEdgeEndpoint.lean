module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceEdgeComparison
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitZeroFaceEndpoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeFunctorRestrictedEndpoint

/-!
概要：第零面の長辺・最後の辺の同じ終点評価を、元の全三角形の終点評価へ接続する。
方針：元の端点包含の厳密な一致と相対制限の合成則を使う。
規約：底の表示変更も保持。使われ方：三辺の指定比較と native 終点比較の同時照合。
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
  (j : Fin 3) (hj : j ≠ 2)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k
local notation "b₂" => ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫
  PointedTransportPrismFamily.diagram (coherentColimitUnitPointedZeroFaceFamily B T k)
local notation "hⱼ" => (stdSimplex.δ j ▷ leftUnstraightening F) ▷ K

include he hS hj in
/-- 長辺・最後の辺の終点でも、元の全パラメータの標的の同じ底を厳密に回収する。 -/
lemma coherentColimitUnitZeroFaceEdgeBase_endpoint :
    (prismEndpoint 1 (leftUnstraightening F) ▷ K) ≫ (hⱼ ≫ b₂) =
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) ≫ Q₂ := by
  rw [← Category.assoc, triangleFamilyEdge_terminal _ _ j hj]
  exact coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS

/-- 元の相対辺を、元の同じ終点の標的の全空間へ評価する。 -/
def coherentColimitUnitZeroFaceEdgeEndpointMap :=
  relativeFunctorRestrictedEndpoint pointedSpaceProjection (hⱼ ≫ b₂)
    (prismEndpoint 1 (leftUnstraightening F) ▷ K) Q₂
    (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (coherentColimitUnitZeroFaceEdgeBase_endpoint B T k H he S hS j hj)

/-- 同じ辺を経る指定終点評価は、元の全三角形の指定終点評価そのもの。 -/
lemma coherentColimitUnitZeroFaceEdgeEndpoint_factor :
    pointedTriangleFamilyEdgeMap D j ≫
      coherentColimitUnitZeroFaceEdgeEndpointMap B T k H he S hS j hj =
    relativeFunctorExtensionEndpoint pointedSpaceProjection b₂
      ((scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ K) (D).boundary (D).projection
      (simplexPrismVertex 2 2 (leftUnstraightening F) ▷ K) Q₂
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
      (coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS) := by
  unfold pointedTriangleFamilyEdgeMap coherentColimitUnitZeroFaceEdgeEndpointMap
  rw [Category.assoc, relativeFunctorRestrictedEndpoint_pre,
    ← relativeFunctorExtensionEndpoint_factor]
  apply congrArg (fun z => relativeFunctorExtensionSpaceι pointedSpaceProjection b₂
    ((scaffoldFirstVertex 2 ▷ leftUnstraightening F) ▷ K) (D).boundary (D).projection ≫ z)
  exact relativeFunctorRestrictedEndpoint_congr pointedSpaceProjection b₂ Q₂
    (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F)
    (triangleFamilyEdge_terminal _ _ j hj)
    (by
      rw [Category.assoc]
      exact coherentColimitUnitZeroFaceEdgeBase_endpoint B T k H he S hS j hj)
    (coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS)

end SerrePositivity.InfinityCategories.F2
