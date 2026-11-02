module

public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedFirstPrism
public import
  SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexLastConstantComparison
/-!
概要：元の第一面の同じ相対比較を、同じ raw 区間頂点の定値族上で保持する。
方針：底と第一面の全族の表示だけを揃え、両側の元の実 prism を保つ。
規約：元の全係数・指定比較・実両端を保持する。
使われ方：第一面の指定自然性正方形と元の中間比較の照合。
-/

@[expose] public section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "β" => intervalMappingUncurry
  (SSet.const (coherentColimitRawIntervalVertex B a) : A ⟶ _)
local notation "W" => coherentColimitApexPointedFirstPrism B T
local notation "W'" => coherentColimitRawTransportPointPrism B a q

/-- 概要：同じ第一面の指定比較の定値区間表示。
方針：元の実二 prism を底の表示だけで移す。
規約：指定値を保持。使われ方：第一辺の自然性正方形。 -/
def coherentColimitApexPointedFirstConstantIso :
    VertexIso (relativeFunctorVertex p β W
      (coherentColimitApexPointedFirstPrism_projection_constant B T))
      (relativeFunctorVertex p β W'
        (coherentColimitRawTransportPointPrism_projection_constant B a q)) :=
  relativeVertexIsoOfEq p (coherentColimitApexPointedFirstIso B T)
    (coherentColimitApexPointedFirstConstantBase B T)
    (spaceSimplexPointedFamily_positive_face s (1 : Fin 2)).symm rfl _ _
/-- 概要：定値区間表示でも同じ第一面の指定比較の値。
方針：表示変更だけを除く。規約：元の指定値を保持。
使われ方：全比較の制限への帰還。 -/
lemma coherentColimitApexPointedFirstConstantIso_heq :
    HEq (coherentColimitApexPointedFirstConstantIso B T)
      (coherentColimitApexPointedFirstIso B T) :=
  relativeVertexIsoOfEq_heq p _ _ _ _ _ _
end
end SerrePositivity.InfinityCategories.F2
