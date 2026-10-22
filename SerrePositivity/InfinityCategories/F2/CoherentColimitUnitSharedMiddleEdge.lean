module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitSharedLongEdge
public import SerrePositivity.InfinityCategories.F2.TetrahedronPrismEdgeIdentities
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceTriangleWitness

/-!
概要：元の全単位三単体の二面で、共有辺 12 の元の指定比較を同定する。
方針：元の全三単体へ戻す実 prism の厳密な一致から始点・終点と指定値を回収する。
規約：全係数と元の指定値を保持。使われ方：四面の式を同じ六辺の比較へ揃える。
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
  {F G J Q₀ Q₁ Q₂ R₁ R₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  {b' : SSet.Homotopy Q₂ R₂} {c' : SSet.Homotopy Q₁ R₂}
  (S : FunctorCompositionTriangle a b c) (R : FunctorCompositionTriangle b b' c')
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry a.h)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 3
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
  (hR : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv R.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "W" => coherentColimitUnitPointedFixedFaceTriangleWitness B T k 3 (by decide) S hS
local notation "f" => coherentColimitUnitPointedFirstEdgeEndpoint B T k a he
local notation "W'" => coherentColimitUnitZeroFaceTriangleWitness B T k a he R hR

/-- 二面で共有する元の辺 12 の実 prism は、全選択を保って厳密に一致する。 -/
lemma coherentColimitUnitSharedMiddleEdge_prism :
    (W).secondWitness.extension = (W').firstWitness.extension := by
  change (stdSimplex.δ (0 : Fin 3) ▷ (leftUnstraightening F ⊗ K)) ≫
      tetrahedronPrismFace (coherentColimitUnitPointedTetrahedronUniversalLift B T k) 3 =
    (stdSimplex.δ (2 : Fin 3) ▷ (leftUnstraightening F ⊗ K)) ≫
      tetrahedronPrismFace (coherentColimitUnitPointedTetrahedronUniversalLift B T k) 0
  exact tetrahedronPrismSharedEdge12
    (coherentColimitUnitPointedTetrahedronUniversalLift B T k)

/-- 同じ共有辺 12 の二つの表示は、元の実終点を厳密に保持する。 -/
lemma coherentColimitUnitSharedMiddleEdge_endpoint :
    (W).secondWitness.endpoint = (W').firstWitness.endpoint :=
  (W).secondWitness.endpoint_eq_of_extension (W').firstWitness
    (coherentColimitUnitSharedMiddleEdge_prism B T k S R he hS hR)

include R hR in
/-- 同じ共有辺 12 の二つの表示は、元の実始点を厳密に保持する。 -/
lemma coherentColimitUnitSharedMiddleEdge_source : (W).middle = f :=
  functorHomotopySource_eq_of_prism b p _ _ (W).middle_projection
    (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k a he) _ _
    (coherentColimitUnitSharedMiddleEdge_prism B T k S R he hS hR)

/-- 同じ共有辺 12 の元の指定比較は、全選択を保って同じ値。 -/
lemma coherentColimitUnitSharedMiddleEdge_comparison :
    HEq (functorHomotopySourceEndpointIso b p (W).middle (W).middle_projection (W).secondWitness)
      (functorHomotopySourceEndpointIso b p f
        (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k a he) (W').firstWitness) :=
  functorHomotopySourceEndpointIso_heq_shared_prism b p _ _ (W).middle_projection
    (coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k a he) _ _
    (coherentColimitUnitSharedMiddleEdge_prism B T k S R he hS hR)

end SerrePositivity.InfinityCategories.F2
