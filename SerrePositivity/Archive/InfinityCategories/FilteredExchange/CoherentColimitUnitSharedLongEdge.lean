module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TetrahedronPrismSharedEdges
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySharedPrism
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitPointedFixedFaceTriangleWitness

/-!
概要：元の全単位三単体の二つの固定面で、共有長辺 03 の元の指定比較を同定する。
方針：同じ元の全三単体の実 prism へ戻し、面の合成の厳密な一致を使う。
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
  {F G J Q₁ R₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  {a' : SSet.Homotopy F R₁} {b' : SSet.Homotopy R₁ Q₂}
  (S : FunctorCompositionTriangle a b c) (R : FunctorCompositionTriangle a' b' c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 1
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
  (hR : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 2
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv R.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "W" => coherentColimitUnitPointedFixedFaceTriangleWitness B T k 1 (by decide) S hS
local notation "W'" => coherentColimitUnitPointedFixedFaceTriangleWitness B T k 2 (by decide) R hR

/-- 二つの固定面の共有長辺は、元の全選択を保った同じ実 prism そのもの。 -/
lemma coherentColimitUnitSharedLongEdge_prism :
    (W).longWitness.extension = (W').longWitness.extension := by
  exact tetrahedronPrismFace_shared_edge (coherentColimitUnitPointedTetrahedronUniversalLift B T k)
    (stdSimplex.δ_comp_δ_self (i := (1 : Fin 3)))

/-- 共有長辺 03 の元の実終点も、同じ全三単体上で厳密に一致する。 -/
lemma coherentColimitUnitSharedLongEdge_endpoint :
    (W).longWitness.endpoint = (W').longWitness.endpoint :=
  (W).longWitness.endpoint_eq_of_extension (W').longWitness
    (coherentColimitUnitSharedLongEdge_prism B T k S R hS hR)

/-- 二面の共有長辺の元の指定比較は、全選択を保って同じ値。 -/
lemma coherentColimitUnitSharedLongEdge_comparison :
    HEq (functorHomotopySourceEndpointIso c p (fst (leftUnstraightening F) K) rfl (W).longWitness)
      (functorHomotopySourceEndpointIso c p (fst (leftUnstraightening F) K) rfl
        (W').longWitness) :=
  functorHomotopySourceEndpointIso_heq_shared_prism c p _ _ rfl rfl _ _
    (coherentColimitUnitSharedLongEdge_prism B T k S R hS hR)

end SerrePositivity.InfinityCategories.F2
