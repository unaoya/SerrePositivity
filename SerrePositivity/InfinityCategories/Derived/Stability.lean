module
public import SerrePositivity.InfinityCategories.Derived.StandardFiberPushout
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport

/-! # D(S) の安定性

概要：任意の四角形の押し出し性と引き戻し性が同値であり、D(S) は安定である。
方針：同じ span/cospan の標準双カルテジアン四角形と比較し、全図式の同型で普遍性を移す。
規約：三角構造と安定性を仮定しない。使われ方：D7 の三角比較、β3〜β5 の対象供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet DGNerve
open scoped Simplicial
variable {S : Type u} [CommRing S]

/-- D(S) の任意の押し出し四角形は引き戻しでもある。 -/
lemma derived_isPullbackSquare_of_isPushoutSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (hF : IsPushoutSquare F) : IsPullbackSquare F := by
  let G := derivedSpanCofiberSquare (pushoutSpan F)
  let c := pushoutCocone G
  let d := rebaseCocone (derivedSpanCofiberSquare_span (pushoutSpan F)) (pushoutCocone F)
  have hc : IsColimitCone c := derivedSpanCofiberSquare_isPushout _
  have hd : IsColimitCone d := rebaseCocone_isColimit _ _ hF
  have e := (coconeFunctorIsoOfVertexIso c d (colimitConeIso c d hc hd)).precomp
    spanCoconeSquareIso.inv
  change FunctorIso (spanCoconeSquareIso.inv ≫ (spanCoconeSquareIso.hom ≫ G))
    (spanCoconeSquareIso.inv ≫ (spanCoconeSquareIso.hom ≫ F)) at e
  simp only [Iso.inv_hom_id_assoc] at e
  exact IsPullbackSquare.of_functorIso (derivedSpanCofiberSquare_isPullback _) e

/-- D(S) の任意の引き戻し四角形は押し出しでもある。 -/
lemma derived_isPushoutSquare_of_isPullbackSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S)
    (hF : IsPullbackSquare F) : IsPushoutSquare F := by
  let G := derivedCospanFiberSquare (pullbackCospan F)
  let c := pullbackCone G
  let d := rebaseCone (derivedCospanFiberSquare_cospan (pullbackCospan F)) (pullbackCone F)
  have hc : IsLimitCone c := derivedCospanFiberSquare_isPullback _
  have hd : IsLimitCone d := rebaseCone_isLimit _ _ hF
  have e := (coneFunctorIsoOfVertexIso c d (limitConeIso c d hc hd)).precomp
    cospanConeSquareIso.inv
  change FunctorIso (cospanConeSquareIso.inv ≫ (cospanConeSquareIso.hom ≫ G))
    (cospanConeSquareIso.inv ≫ (cospanConeSquareIso.hom ≫ F)) at e
  simp only [Iso.inv_hom_id_assoc] at e
  exact IsPushoutSquare.of_functorIso (derivedCospanFiberSquare_isPushout _) e

/-- 任意の D(S) の四角形について押し出し性と引き戻し性は同値。 -/
theorem derived_isPullbackSquare_iff_isPushoutSquare
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ derivedInfinityCategory S) :
    IsPullbackSquare F ↔ IsPushoutSquare F :=
  ⟨derived_isPushoutSquare_of_isPullbackSquare F, derived_isPullbackSquare_of_isPushoutSquare F⟩

/-- 任意の可換環上の非有界導来 ∞ 圏は安定である。 -/
instance derivedInfinityCategory_isStable (S : Type u) [CommRing S] :
    IsStable (derivedInfinityCategory S) where
  toHasZeroVertex := inferInstance
  fiber_exists := derivedInfinityCategory_fiber_exists
  cofiber_exists := derivedInfinityCategory_cofiber_exists
  fiber_iff_cofiber t := derived_isPullbackSquare_iff_isPushoutSquare t.square

end SerrePositivity.InfinityCategories
