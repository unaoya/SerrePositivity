module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedLastPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedEdgeComparisons

/-!
概要：元の最後辺の同じ指定相対比較を、同じ raw 区間頂点の定値族上で読む。
方針：底の厳密な等式だけで表示変更し、両側の実 prism と元の指定値を保持する。
規約：全初点係数を保持。使われ方：始点も動く指定比較の自然性の実最後辺への適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ元の raw 輸送 prism も、同じ指定区間頂点の定値族を厳密に被覆する。 -/
lemma coherentColimitRawTransportPointPrism_projection_constant (B : SSet.{u})
    {G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (b : SSet.Homotopy G J) {K : SSet.{u + 1}}
    (f : K ⟶ vertexFiber pointedSpaceProjection (coherentDiagramTotalCocone G).vertex) :
    coherentColimitRawTransportPointPrism B b f ≫ pointedSpaceProjection =
      intervalMappingUncurry (SSet.const (coherentColimitRawIntervalVertex B b) : K ⟶ _) := by
  rw [coherentColimitRawTransportPointPrism_projection]
  exact (coherentColimitRawConstantInterval_uncurry B b K).symm

variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "v" => (SSet.const (coherentColimitRawIntervalVertex B b) : A ⟶ _)
local notation "β" => intervalMappingUncurry v
local notation "W" => coherentColimitApexPointedLastPrism B T
local notation "W'" => coherentColimitRawTransportPointPrism B b
  (q ≫ coherentColimitRawFiberTransport B a)

/-- 元の最後面の底と、元の同じ指定区間頂点の定値族の底の一致。 -/
lemma coherentColimitApexPointedLastConstantBase :
    fst (Δ[1] : SSet.{u + 1}) A ≫ SSet.yonedaEquiv.symm (SpaceInfinity.δ 0 s) = β := by
  rw [coherentColimitApexTriangle_last]
  exact (coherentColimitRawConstantInterval_uncurry B b A).symm

/-- 底の表示だけを揃えた元の最後辺の指定相対比較。両実 prism は変更しない。 -/
def coherentColimitApexPointedLastConstantIso :
    VertexIso (relativeFunctorVertex p β W
      (coherentColimitApexPointedLastPrism_projection_constant B T))
      (relativeFunctorVertex p β W'
        (coherentColimitRawTransportPointPrism_projection_constant B b
          (q ≫ coherentColimitRawFiberTransport B a))) :=
  relativeVertexIsoOfEq p (coherentColimitApexPointedLastIso B T)
    (coherentColimitApexPointedLastConstantBase B T) rfl rfl _ _

/-- 定値区間上で読んでも、元の最後辺の同じ指定比較の値を保持する。 -/
lemma coherentColimitApexPointedLastConstantIso_heq :
    HEq (coherentColimitApexPointedLastConstantIso B T)
      (coherentColimitApexPointedLastIso B T) :=
  relativeVertexIsoOfEq_heq p _ _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
