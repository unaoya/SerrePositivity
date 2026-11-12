module

public import SerrePositivity.EInfinity.SimplicialLocalization.LocalizationNerveSource
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationEquivalenceTransport

/-!
# 元の反転関手圏への全前合成と既存 nerve の比較

概要：既存 localizationNerve への写像の普遍性を実 hammock 側へ還元する。
方針：同じ指定辺集合への前合成を、元の Kan nerve 同値の前合成で厳密に因子化する。
規約：全 quasicategory 標的と全部分関手圏を扱う。普遍性自体は未供給。
使われ方：実 hammock の ∞ 局所化を既存 CAlg_R へ移す最終工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory MonoidalClosed SerrePositivity.InfinityCategories
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

lemma localizationNerveSourceMap_precomposition (E : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (localizationNerveSourceMap C) (weakNerveEdges C)
        (localizationNerveSourceMap_inverts C) E =
      (pre (kanHammockLocalizationEquivalence C).hom).app E ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (hammockLocalizationNerveMap C) (weakNerveEdges C)
          (hammockLocalizationNerveMap_inverts C) E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_comp_equivalence _ _ _ _ E

lemma localizationNerveSourceMap_isLocalization_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (localizationNerveSourceMap C) (weakNerveEdges C) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap C) (weakNerveEdges C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_comp_equivalence_iff _ _
    (hammockLocalizationNerveMap_inverts C) (kanHammockLocalizationEquivalence C)

end SerrePositivity.EInfinity.SimplicialLocalization
