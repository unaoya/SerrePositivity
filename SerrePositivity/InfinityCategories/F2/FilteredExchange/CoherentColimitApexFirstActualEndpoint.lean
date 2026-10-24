module

public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexFirstConstantComparison
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismEndpointComparisons
public import
SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitApexPointedEndpointComparisons
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativePrismEndpointImageDataEquality
public import
  SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceSimplexPointedRestrictionEndpointImage

/-!
概要：元の実第一辺の指定相対比較の終点像を、同じ全三角形の中間比較へ同定する。
方針：底と実 prism の等式を明示し、同じ全比較の制限と同じ端点評価へ戻す。
規約：元の指定値と全初点係数を保持。使われ方：元の第一辺値と中間比較の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)
local notation "p" => pointedSpaceProjection
local notation "s" => coherentColimitApexTriangle B T
local notation "A" => spaceSimplexPointedCoefficients s
local notation "q" => coherentColimitApexCoefficientMap B T
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone G)
local notation "β" => intervalMappingUncurry
  (SSet.const (coherentColimitRawIntervalVertex B a) : A ⟶ _)
local notation "W" => coherentColimitApexPointedFirstPrism B T
local notation "f" => coherentColimitApexMiddleCoefficientMap B T
local notation "f'" =>
  q ≫ coherentColimitRawFiberTransport B a
local notation "W'" => coherentColimitRawTransportPointPrism B a q
local notation "hW" => coherentColimitApexPointedFirstPrism_projection_constant B T
local notation "hW'" => coherentColimitRawTransportPointPrism_projection_constant B a q
local notation "e" => coherentColimitApexPointedFirstConstantIso B T

/-- 概要：元の実第一辺の同じ指定比較の実終点像は元の中間比較。
方針：同じ全比較の同じ頂点評価へ戻す。
規約：指定値と全係数を保持。使われ方：第一辺の指定正方形。 -/
lemma coherentColimitApexFirstActualEndpointIso_eq_middle :
    relativePrismActualEndpointIso p β x (intervalMappingUncurry_one _) W W' hW hW' f f'
      (coherentColimitApexPointedFirstPrism_finish B T)
      (coherentColimitRawTransportPointPrism_finish B a q) e =
        coherentColimitApexPointedMiddleEndpointIso B T := by
  let r := stdSimplex.δ (2 : Fin 3) ▷ A
  let γ := fst Δ[2] A ≫ SSet.yonedaEquiv.symm s
  let L := coherentColimitRawUniversalTrianglePrism B T q
  have hk : prismEndpoint 1 A ≫ r = simplexPrismVertex 2 1 A := by
    apply SSet.hom_ext
    intro n
    rfl
  have hz : prismEndpoint 1 A ≫ (r ≫ γ) = SSet.const x :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ γ) hk).trans (coherentColimitApexPointedMiddle_base B T))
  have he : HEq e (coherentColimitApexPointedFamilyRestrictionIso B T r) :=
    (coherentColimitApexPointedFirstConstantIso_heq B T).trans
      ((coherentColimitApexPointedFirstIso_heq B T).trans
        (coherentColimitApexPointedFaceIso_heq B T 2))
  have hd := relativePrismEndpointImage_heq_of_dataEq p β (r ≫ γ)
    W W' (r ≫ spaceSimplexPointedFamily s) (r ≫ L) hW hW'
    (by rw [Category.assoc, spaceSimplexPointedFamily_projection])
    (by rw [Category.assoc, coherentColimitApexPointedFamily_projection])
    e (coherentColimitApexPointedFamilyRestrictionIso B T r) 1 x
    (intervalMappingUncurry_one _) hz
    ((coherentColimitApexPointedFirstConstantBase B T).symm.trans
      (spaceTrianglePointedFace_base s A 2).symm) rfl
    (coherentColimitRawUniversalTrianglePrism_first B T q).symm he
  have ht := spaceSimplexPointedRestrictionEndpointImage_heq_endpoint s L
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T) r 1 (simplexPrismVertex 2 1 A) hk x
    (coherentColimitApexPointedMiddle_base B T) f f'
    (coherentColimitApexMiddleCoefficientMap_ι B T).symm
    (coherentColimitApexPointedMiddle_endpoint B T)
  unfold relativePrismActualEndpointIso
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans (hd.trans ht))

end SerrePositivity.InfinityCategories.F2
