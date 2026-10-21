module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitPointedFixedFaceLongWitness
public import SerrePositivity.InfinityCategories.F2.RelativeExtensionEndpointComposition

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
local notation "C" => leftUnstraightening F ⊗ K
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "v" => simplexPrismVertex 0 0 C ≫ Iso.inv (α_ Δ[0] (leftUnstraightening F) K) ≫
  PointedTransportPrismFamily.boundary D
local notation "b₁" => (stdSimplex.δ (1 : Fin 3) ▷ C) ≫
  Iso.inv (α_ Δ[2] (leftUnstraightening F) K) ≫
  ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫ PointedTransportPrismFamily.diagram D

local notation "X" => coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS false
local notation "Y" => coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS true

/-- 同じ元の指定長辺の普遍証拠を、元の二面の共通の底・全初期値で保持する。 -/
def coherentColimitUnitPointedFixedFaceCanonicalLongWitness :=
  (functorHomotopySourceCanonicalWitness c p (fst (leftUnstraightening F) K) rfl).transportData
    (coherentColimitUnitPointedFixedFaceLong_base B T k j hj S hS).symm
    (coherentColimitUnitPointedFixedFaceLong_initial B T k j hj S hS).symm rfl

local notation "Z" => coherentColimitUnitPointedFixedFaceCanonicalLongWitness B T k j hj S hS

/-- 元の普遍長辺から元の実二面の長辺への、同じ全初期値の指定比較。 -/
def coherentColimitUnitPointedFixedFaceLongSourceIso :=
  (Z).iso X (prismEndpoint_zero_leftAnodyne C) (X).initial_base (X).endpoint_base

/-- 元の実二面の長辺から元の指定三角形の長辺への、同じ全初期値の指定比較。 -/
def coherentColimitUnitPointedFixedFaceLongTriangleIso :=
  (X).iso Y (prismEndpoint_zero_leftAnodyne C) (X).initial_base (X).endpoint_base

/-- 元の普遍長辺から元の指定三角形の長辺への、同じ全初期値の直接比較。 -/
def coherentColimitUnitPointedFixedFaceLongCompositeIso :=
  (Z).iso Y (prismEndpoint_zero_leftAnodyne C) (X).initial_base (X).endpoint_base

/-- 元の三長辺証拠の同じ指定比較は、中間の実長辺を消去して厳密に合成する。 -/
lemma coherentColimitUnitPointedFixedFaceLongIso_trans :
    coherentColimitUnitPointedFixedFaceLongSourceIso B T k j hj S hS ≪≫
      coherentColimitUnitPointedFixedFaceLongTriangleIso B T k j hj S hS =
      coherentColimitUnitPointedFixedFaceLongCompositeIso B T k j hj S hS :=
  RelativeExtensionEndpointWitness.iso_trans Z X Y (prismEndpoint_zero_leftAnodyne C)
    (X).initial_base (X).endpoint_base

/-- 同じ実長辺と実終点を保つ表示変更は、元の指定始域比較の値を保つ。 -/
lemma coherentColimitUnitPointedFixedFaceLongSourceIso_heq_homotopy :
    HEq (coherentColimitUnitPointedFixedFaceLongSourceIso B T k j hj S hS)
      (functorHomotopySourceEndpointIso c p (fst (leftUnstraightening F) K) rfl
        (coherentColimitUnitPointedFixedFaceHomotopyWitness B T k j hj S hS false)) :=
  RelativeExtensionEndpointWitness.iso_heq_of_dataEq Z X
    (functorHomotopySourceCanonicalWitness c p (fst (leftUnstraightening F) K) rfl)
    (coherentColimitUnitPointedFixedFaceHomotopyWitness B T k j hj S hS false)
    (coherentColimitUnitPointedFixedFaceLong_base B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLong_initial B T k j hj S hS) rfl rfl rfl rfl rfl
    (prismEndpoint_zero_leftAnodyne C) (X).initial_base
    (coherentColimitUnitPointedFixedFaceHomotopyWitness B T k j hj S hS false).initial_base
    (X).endpoint_base
    (coherentColimitUnitPointedFixedFaceHomotopyWitness B T k j hj S hS false).endpoint_base

end SerrePositivity.InfinityCategories.F2
