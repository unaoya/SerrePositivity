module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceEndpointIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceEdges
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedTriangleFamilyLongWitness
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopySourceComponent

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

/-- 元の二面と指定三角形を、同じ全係数・始点・底の長辺証拠へ制限する。 -/
def coherentColimitUnitPointedFixedFaceLongWitness (original : Bool) :=
  let wFull := coherentColimitUnitPointedFixedFaceEndpointWitness B T k j hj S hS original
  pointedTriangleFamilyLongEndpointWitness D wFull.extension wFull.initial wFull.over Q₂
    p wFull.endpoint wFull.endpoint_over wFull.evaluate

/-- 固定始点の長辺の全初期値は、元の全空間射影の pointed 成分そのもの。 -/
lemma coherentColimitUnitPointedFixedFaceLong_initial :
    v = fst (leftUnstraightening F) K ≫ pullback.fst pointedSpaceProjection F := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 固定始点の同じ長辺の全底は、元の指定長辺変換の全図式。 -/
lemma coherentColimitUnitPointedFixedFaceLong_base :
    b₁ = (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry c.h) := by
  calc
    _ = (Δ[1] ◁ p) ≫ functorSimplexDiagram (stdSimplex.δ (1 : Fin 3) ≫ S.diagram) := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = _ := by rw [S.face_one]

/-- 同じ実長辺と実終点を、元の指定長辺変換の底・初期値の表示で保持する。 -/
def coherentColimitUnitPointedFixedFaceHomotopyWitness (original : Bool) :=
  (coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS original).transportData
    (coherentColimitUnitPointedFixedFaceLong_base B T k j hj S hS)
    (coherentColimitUnitPointedFixedFaceLong_initial B T k j hj S hS) rfl

end SerrePositivity.InfinityCategories.F2
