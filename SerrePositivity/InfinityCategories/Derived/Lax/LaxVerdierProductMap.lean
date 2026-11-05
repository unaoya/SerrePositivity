module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productMapSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i r)

def laxQuotientProductMap : Binary.obj (value Φ C) (value Φ D) ⟶ value Φ Q :=
  SpectrumHo.representative ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom hΦ) p q r)

lemma laxQuotientProductMap_hom : SpectrumHo.hom ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r) =
    (_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionDifferenceHom hΦ) p q r := SpectrumHo.hom_representative _

lemma laxQuotientProductMap_right_comm :
    SpectrumHo.hom ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r) ≫
        (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)).inv =
      ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionMiddleIso hΦ) p q i r h).inv ≫
        squareHoRight ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (hΦ := hΦ)) p q i r h).square := by
  apply (cancel_epi ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionMiddleIso hΦ) p q i r h).hom).mp
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap_hom, _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionMiddleIso_right,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

lemma exists_laxQuotientProductArrowIso_with_endpoints :
    ∃ e : FunctorIso
    (SSet.yonedaEquiv.symm (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).edge)
    (squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (hΦ := hΦ)) p q i r h).square),
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
        (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionMiddleIso hΦ) p q i r h).inv ∧
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
        (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)).inv := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap_right_comm hΦ) p q i r h
  have e := _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.exists_arrowFunctorIso_with_endpoints (X := Sp.{u})
    (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).toTruncated
    (squareRightArrow ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (hΦ := hΦ)) p q i r h).square)
    ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionMiddleIso hΦ) p q i r h).symm
    (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)).symm hc
  have heq : SSet.yonedaEquiv.symm
      (squareRightArrow ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (hΦ := hΦ)) p q i r h).square).edge =
      squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (hΦ := hΦ)) p q i r h).square := by
    rw [squareRightArrow_edge, SSet.yonedaEquiv.symm_apply_apply]
  exact heq ▸ e

def laxQuotientProductArrowIso : FunctorIso
    (SSet.yonedaEquiv.symm (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).edge)
    (squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (hΦ := hΦ)) p q i r h).square) :=
  Classical.choose ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.exists_laxQuotientProductArrowIso_with_endpoints hΦ) p q i r h)

lemma nonempty_laxQuotientProductArrowIso : Nonempty (FunctorIso
    (SSet.yonedaEquiv.symm (coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap hΦ) p q r)).edge)
    (squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle (hΦ := hΦ)) p q i r h).square)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso hΦ) p q i r h⟩

lemma laxQuotientProductArrowIso_source :
    Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))))).toFunctor.map
        ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso hΦ) p q i r h).hom) =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProjectionMiddleIso hΦ) p q i r h).inv :=
  (Classical.choose_spec ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.exists_laxQuotientProductArrowIso_with_endpoints hΦ) p q i r h)).1

lemma laxQuotientProductArrowIso_target :
    Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := Sp.{u})
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))))).toFunctor.map
        ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso hΦ) p q i r h).hom) =
      Arrow.mk (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Derived.Lax.laxQuotientVerdierSequence p q i r h)).inv :=
  (Classical.choose_spec ((_root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.exists_laxQuotientProductArrowIso_with_endpoints hΦ) p q i r h)).2

end SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.exists_laxQuotientProductArrowIso_with_endpoints := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.exists_laxQuotientProductArrowIso_with_endpoints

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso_source := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso_target := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductMap := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductMap_hom := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductMap_right_comm := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductMap_right_comm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.nonempty_laxQuotientProductArrowIso := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.nonempty_laxQuotientProductArrowIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productMapSimplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.productMapSimplicialCategory := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.productMapSimplicialCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Lax.IsLocalizingInvariant.laxQuotientProductArrowIso._proof_1
