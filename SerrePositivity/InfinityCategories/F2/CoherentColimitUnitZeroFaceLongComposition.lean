module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceCanonicalLong
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionEndpointComposition

/-!
概要：元の普遍長辺・第零面の実長辺・指定三角形の長辺の比較を、同じ全空間で合成する。
方針：三証拠の同じ底と初期値を回収し、既存の指定終点比較の合成則を適用する。
規約：指定比較の値を保持。使われ方：元の指定三角形比較の前合成の整合式。
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
local notation "b₁" => (stdSimplex.δ (1 : Fin 3) ▷ C) ≫
  Iso.inv (α_ Δ[2] (leftUnstraightening F) K) ≫
  ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫
  PointedTransportPrismFamily.diagram (coherentColimitUnitPointedZeroFaceFamily B T k)
local notation "v" => simplexPrismVertex 0 0 C ≫ Iso.inv (α_ Δ[0] (leftUnstraightening F) K) ≫
  PointedTransportPrismFamily.boundary (coherentColimitUnitPointedZeroFaceFamily B T k)
local notation "Z" => coherentColimitUnitZeroFaceCanonicalLongWitness B T k H he S hS
local notation "X" => coherentColimitUnitZeroFaceLongWitness B T k H he S hS false
local notation "Y" => coherentColimitUnitZeroFaceLongWitness B T k H he S hS true

include he hS in
/-- 同じ長辺の三証拠の全初期値は、同じ元の長辺の底を被覆する。 -/
lemma coherentColimitUnitZeroFaceLong_base_initial :
    v ≫ pointedSpaceProjection = prismEndpoint 0 C ≫ b₁ := by
  rw [← (Y).initial, Category.assoc, (Y).over]

include he hS in
/-- 同じ長辺の三証拠の底の終点は、同じ元の全パラメータの標的図式。 -/
lemma coherentColimitUnitZeroFaceLong_base_endpoint :
    prismEndpoint 1 C ≫ b₁ =
      (fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F) ≫ Q₂ :=
  coherentColimitUnitZeroFaceBase_endpoint B T k H he S hS

local notation "hv" => coherentColimitUnitZeroFaceLong_base_initial B T k H he S hS
local notation "hj" => coherentColimitUnitZeroFaceLong_base_endpoint B T k H he S hS

/-- 元の普遍長辺から実長辺への、同じ全初期値を持つ指定始域比較。 -/
def coherentColimitUnitZeroFaceLongSourceIso :=
  (Z).iso X (prismEndpoint_zero_leftAnodyne C) hv hj

/-- 元の実長辺から指定三角形の長辺への、同じ全パラメータの指定終点比較。 -/
def coherentColimitUnitZeroFaceLongTriangleIso :=
  (X).iso Y (prismEndpoint_zero_leftAnodyne C) hv hj

/-- 元の普遍長辺から指定三角形の長辺への、同じ全初期値の直接の指定比較。 -/
def coherentColimitUnitZeroFaceLongCompositeIso :=
  (Z).iso Y (prismEndpoint_zero_leftAnodyne C) hv hj

/-- 三つの元の長辺証拠の指定比較は、中間の実長辺を消去して厳密に合成する。 -/
lemma coherentColimitUnitZeroFaceLongIso_trans :
    coherentColimitUnitZeroFaceLongSourceIso B T k H he S hS ≪≫
      coherentColimitUnitZeroFaceLongTriangleIso B T k H he S hS =
      coherentColimitUnitZeroFaceLongCompositeIso B T k H he S hS :=
  RelativeExtensionEndpointWitness.iso_trans Z X Y (prismEndpoint_zero_leftAnodyne C) hv hj

end SerrePositivity.InfinityCategories.F2
