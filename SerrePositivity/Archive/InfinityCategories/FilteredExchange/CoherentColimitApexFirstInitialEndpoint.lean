module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexFirstConstantComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismInitialEndpoint
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitApexPointedInitialEndpoint
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativePrismEndpointImageDataEquality
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedRestrictionEndpointImage

/-!
概要：元の実第一辺の指定相対比較の始点像は、同じ全初期係数の恒等比較となる。
方針：底と実 prism の等式を明示し、同じ全比較の制限と同じ端点評価へ戻す。
規約：元の指定値と全初点係数を保持。使われ方：第一辺の native 像の恒等性。
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
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "β" => intervalMappingUncurry
  (SSet.const (coherentColimitRawIntervalVertex B a) : A ⟶ _)
local notation "W" => coherentColimitApexPointedFirstPrism B T
local notation "f" => q
local notation "f'" => q
local notation "W'" => coherentColimitRawTransportPointPrism B a q
local notation "hW" => coherentColimitApexPointedFirstPrism_projection_constant B T
local notation "hW'" => coherentColimitRawTransportPointPrism_projection_constant B a q
local notation "e" => coherentColimitApexPointedFirstConstantIso B T

/-- 概要：元の実第一辺の同じ指定比較の実初点像は元の恒等比較。
方針：固定した同じ全初点の評価へ戻す。
規約：全係数と指定値を保持。使われ方：第一辺の native 像の消去。 -/
lemma coherentColimitApexFirstInitialEndpointIso_eq_refl :
    relativePrismInitialEndpointIso p β x (intervalMappingUncurry_zero _) W W' hW hW' f f'
      (coherentColimitApexPointedFirstPrism_start B T)
      (coherentColimitRawTransportPointPrism_start B a q) e =
        Iso.refl (SSet.HomotopyCategory.mk (functorVertex q)) := by
  let r := stdSimplex.δ (2 : Fin 3) ▷ A
  let γ := fst Δ[2] A ≫ SSet.yonedaEquiv.symm s
  let L := coherentColimitRawUniversalTrianglePrism B T q
  have hk : prismEndpoint 0 A ≫ r = simplexPrismVertex 2 0 A := by
    apply SSet.hom_ext
    intro n
    rfl
  have hz : prismEndpoint 0 A ≫ (r ≫ γ) = SSet.const x :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ γ) hk).trans (coherentColimitApexPointedInitial_base B T))
  have he : HEq e (coherentColimitApexPointedFamilyRestrictionIso B T r) :=
    (coherentColimitApexPointedFirstConstantIso_heq B T).trans
      ((coherentColimitApexPointedFirstIso_heq B T).trans
        (coherentColimitApexPointedFaceIso_heq B T 2))
  have hd := relativePrismEndpointImage_heq_of_dataEq p β (r ≫ γ)
    W W' (r ≫ spaceSimplexPointedFamily s) (r ≫ L) hW hW'
    (by rw [Category.assoc, spaceSimplexPointedFamily_projection])
    (by rw [Category.assoc, coherentColimitApexPointedFamily_projection])
    e (coherentColimitApexPointedFamilyRestrictionIso B T r) 0 x
    (intervalMappingUncurry_zero _) hz
    ((coherentColimitApexPointedFirstConstantBase B T).symm.trans
      (spaceTrianglePointedFace_base s A 2).symm) rfl
    (coherentColimitRawUniversalTrianglePrism_first B T q).symm he
  have hs : simplexPrismVertex 2 0 A ≫ spaceSimplexPointedFamily s =
      q ≫ vertexFiberι p x :=
    (spaceTrianglePointedFamily_source_action s).trans
      (coherentColimitApexCoefficientMap_ι B T).symm
  have hs' : simplexPrismVertex 2 0 A ≫ L = q ≫ vertexFiberι p x := by
    rw [← hk, Category.assoc, coherentColimitRawUniversalTrianglePrism_first,
      coherentColimitRawTransportPointPrism_start]
  have ht := spaceSimplexPointedRestrictionEndpointImage_heq_endpoint s L
    (coherentColimitApexPointedFamily_projection B T)
    (coherentColimitApexPointedFamily_initial B T) r 0 (simplexPrismVertex 2 0 A) hk x
    (coherentColimitApexPointedInitial_base B T) q q hs hs'
  unfold relativePrismInitialEndpointIso
  have ht' := ht.trans (heq_of_eq
    (coherentColimitApexPointedInitialEndpointIso_eq_refl B T hs hs'))
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans (hd.trans ht'))
end SerrePositivity.InfinityCategories.F2
