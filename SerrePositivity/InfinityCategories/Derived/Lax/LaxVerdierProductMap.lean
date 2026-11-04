module

public import SerrePositivity.InfinityCategories.Derived.Lax.LaxVerdierProjectionFiber
public import SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowIsoEndpointControl

/-!
概要：d8 の積から商の値への実 BF 射と、元の右辺との coherent な比較。
方針：両射影を保つ中項の同型を使い、h Sp の可換四角形を区間関手の同型に実現する。
規約：射の整数 π の一致だけでは代用しない。使われ方：実 product fiber 四角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productMapSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {Φ : StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)
  (i : ExactMap A (laxCategory p q)) (r : ExactMap (laxCategory p q) Q)
  (h : IsVerdierSequence i r)

def laxQuotientProductMap : Binary.obj (value Φ C) (value Φ D) ⟶ value Φ Q :=
  SpectrumHo.representative (hΦ.laxQuotientProjectionDifferenceHom p q r)

lemma laxQuotientProductMap_hom : SpectrumHo.hom (hΦ.laxQuotientProductMap p q r) =
    hΦ.laxQuotientProjectionDifferenceHom p q r := SpectrumHo.hom_representative _

lemma laxQuotientProductMap_right_comm :
    SpectrumHo.hom (hΦ.laxQuotientProductMap p q r) ≫
        (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).inv =
      (hΦ.laxQuotientProjectionMiddleIso p q i r h).inv ≫
        squareHoRight (hΦ.laxQuotientFiberTriangle p q i r h).square := by
  apply (cancel_epi (hΦ.laxQuotientProjectionMiddleIso p q i r h).hom).mp
  rw [← Category.assoc, laxQuotientProductMap_hom, laxQuotientProjectionMiddleIso_right,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

lemma exists_laxQuotientProductArrowIso_with_endpoints :
    ∃ e : FunctorIso
    (SSet.yonedaEquiv.symm (coherentNerveEdge (hΦ.laxQuotientProductMap p q r)).edge)
    (squareRightEdge ≫ (hΦ.laxQuotientFiberTriangle p q i r h).square),
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
        (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk (hΦ.laxQuotientProjectionMiddleIso p q i r h).inv ∧
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
        (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).inv := by
  have hc := hΦ.laxQuotientProductMap_right_comm p q i r h
  have e := exists_arrowFunctorIso_with_endpoints (X := Sp.{u})
    (coherentNerveEdge (hΦ.laxQuotientProductMap p q r)).toTruncated
    (squareRightArrow (hΦ.laxQuotientFiberTriangle p q i r h).square)
    (hΦ.laxQuotientProjectionMiddleIso p q i r h).symm
    (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).symm hc
  have heq : SSet.yonedaEquiv.symm
      (squareRightArrow (hΦ.laxQuotientFiberTriangle p q i r h).square).edge =
      squareRightEdge ≫ (hΦ.laxQuotientFiberTriangle p q i r h).square := by
    rw [squareRightArrow_edge, SSet.yonedaEquiv.symm_apply_apply]
  exact heq ▸ e

def laxQuotientProductArrowIso : FunctorIso
    (SSet.yonedaEquiv.symm (coherentNerveEdge (hΦ.laxQuotientProductMap p q r)).edge)
    (squareRightEdge ≫ (hΦ.laxQuotientFiberTriangle p q i r h).square) :=
  Classical.choose (hΦ.exists_laxQuotientProductArrowIso_with_endpoints p q i r h)

lemma nonempty_laxQuotientProductArrowIso : Nonempty (FunctorIso
    (SSet.yonedaEquiv.symm (coherentNerveEdge (hΦ.laxQuotientProductMap p q r)).edge)
    (squareRightEdge ≫ (hΦ.laxQuotientFiberTriangle p q i r h).square)) :=
  ⟨hΦ.laxQuotientProductArrowIso p q i r h⟩

lemma laxQuotientProductArrowIso_source :
    Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))))).toFunctor.map
        (hΦ.laxQuotientProductArrowIso p q i r h).hom) =
      Arrow.mk (hΦ.laxQuotientProjectionMiddleIso p q i r h).inv :=
  (Classical.choose_spec (hΦ.exists_laxQuotientProductArrowIso_with_endpoints p q i r h)).1

lemma laxQuotientProductArrowIso_target :
    Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))))).toFunctor.map
        (hΦ.laxQuotientProductArrowIso p q i r h).hom) =
      Arrow.mk (hΦ.fiberRightIso (laxQuotientVerdierSequence p q i r h)).inv :=
  (Classical.choose_spec (hΦ.exists_laxQuotientProductArrowIso_with_endpoints p q i r h)).2

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
