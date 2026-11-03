module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitSharedLongEdge
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceTriangleWitness

/-!
概要：元の全単位三単体の二面で、共有辺 02 の元の指定比較を同定する。
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
  {a' : SSet.Homotopy F R₁} {b' : SSet.Homotopy R₁ Q₁}
  (S : FunctorCompositionTriangle a b c) (R : FunctorCompositionTriangle a' b' a)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 1
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
  (hR : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 3
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv R.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "W" => coherentColimitUnitPointedFixedFaceTriangleWitness B T k 1 (by decide) S hS
local notation "W'" => coherentColimitUnitPointedFixedFaceTriangleWitness B T k 3 (by decide) R hR

/-- 二面で共有する元の辺 02 の実 prism は、全選択を保って厳密に一致する。 -/
lemma coherentColimitUnitSharedInitialDiagonalEdge_prism :
    (W).firstWitness.extension = (W').longWitness.extension := by
  exact tetrahedronPrismFace_shared_edge (coherentColimitUnitPointedTetrahedronUniversalLift B T k)
    (stdSimplex.δ_comp_δ (show (1 : Fin 3) ≤ 2 by decide)).symm

/-- 同じ共有辺 02 の二つの表示は、元の実終点を厳密に保持する。 -/
lemma coherentColimitUnitSharedInitialDiagonalEdge_endpoint :
    (W).firstWitness.endpoint = (W').longWitness.endpoint :=
  (W).firstWitness.endpoint_eq_of_extension (W').longWitness
    (coherentColimitUnitSharedInitialDiagonalEdge_prism B T k S R hS hR)

/-- 同じ共有辺 02 の元の指定比較は、全選択を保って同じ値。 -/
lemma coherentColimitUnitSharedInitialDiagonalEdge_comparison :
    HEq (functorHomotopySourceEndpointIso a p (fst (leftUnstraightening F) K) rfl (W).firstWitness)
      (functorHomotopySourceEndpointIso a p (fst (leftUnstraightening F) K) rfl (W').longWitness) :=
  functorHomotopySourceEndpointIso_heq_shared_prism a p _ _ rfl rfl _ _
    (coherentColimitUnitSharedInitialDiagonalEdge_prism B T k S R hS hR)

end SerrePositivity.InfinityCategories.F2
