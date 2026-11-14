module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.LaxVerdierProjectionFiber
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.ArrowIsoEndpointControl

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax
open _root_.SerrePositivity.KST.LocalizingInvariants
open _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
local instance productMapSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hΦ : IsLocalizingInvariant Φ)
  {C D E A Q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A (laxCategory p q)) (r : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (laxCategory p q) Q)
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i r)

def laxQuotientProductMap : Binary.obj (value Φ C) (value Φ D) ⟶ value Φ Q :=
  SpectrumHo.representative ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q r)

lemma laxQuotientProductMap_hom : SpectrumHo.hom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionDifferenceHom hΦ) p q r := SpectrumHo.hom_representative _

lemma laxQuotientProductMap_right_comm :
    SpectrumHo.hom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r) ≫
        (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).inv =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).inv ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square := by
  apply (cancel_epi ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).hom).mp
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap_hom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso_right,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

lemma exists_laxQuotientProductArrowIso_with_endpoints :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square),
      Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{u})
        (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).inv ∧
      Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{u})
        (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))))).toFunctor.map e.hom) =
          Arrow.mk (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).inv := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap_right_comm hΦ) p q i r h
  have e := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.exists_arrowFunctorIso_with_endpoints (X := Sp.{u})
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square)
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).symm
    (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).symm hc
  have heq : SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, SSet.yonedaEquiv.symm_apply_apply]
  exact heq ▸ e

def laxQuotientProductArrowIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square) :=
  Classical.choose ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.exists_laxQuotientProductArrowIso_with_endpoints hΦ) p q i r h)

lemma nonempty_laxQuotientProductArrowIso : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap hΦ) p q r)).edge)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.IsLocalizingInvariant.laxQuotientFiberTriangle p q i r h hΦ)).square)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso hΦ) p q i r h⟩

lemma laxQuotientProductArrowIso_source :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{u})
      (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2))))).toFunctor.map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso hΦ) p q i r h).hom) =
      Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProjectionMiddleIso hΦ) p q i r h).inv :=
  (Classical.choose_spec ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.exists_laxQuotientProductArrowIso_with_endpoints hΦ) p q i r h)).1

lemma laxQuotientProductArrowIso_target :
    Arrow.mk ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Sp.{u})
      (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2))))).toFunctor.map
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso hΦ) p q i r h).hom) =
      Arrow.mk (hΦ.fiberRightIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientVerdierSequence p q i r h)).inv :=
  (Classical.choose_spec ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.exists_laxQuotientProductArrowIso_with_endpoints hΦ) p q i r h)).2

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.exists_laxQuotientProductArrowIso_with_endpoints := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.exists_laxQuotientProductArrowIso_with_endpoints

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso_source := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso_target := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductMap := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductMap_hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductMap_right_comm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductMap_right_comm

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.nonempty_laxQuotientProductArrowIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.nonempty_laxQuotientProductArrowIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.productMapSimplicialCategory (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.productMapSimplicialCategory := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.productMapSimplicialCategory

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant.laxQuotientProductArrowIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Lax.laxQuotientProductArrowIso._proof_1
