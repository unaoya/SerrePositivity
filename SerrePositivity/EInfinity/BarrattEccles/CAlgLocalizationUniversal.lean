module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRightKanUnit
public import SerrePositivity.EInfinity.BarrattEccles.CAlgLocalizationSource
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RightKanCriterion

/-!
# 既存 CAlg_R の元の ∞ 局所化普遍性

概要：任意 quasicategory 標的の全反転関手 ∞ 圏への前合成を同値と証明する。
方針：実右 Kan 局所極限・標準条件・元の実単位の可逆性を使い、元の DK nerve へ移す。
規約：既存 CAlg_R・元の局所化写像・元の弱同値を保持する。
使われ方：E2b γ2 e の普遍性本体。U・離散対象・G1′ は後続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SimplicialLocalization
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

lemma cofibrantHammockLocalization_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
      (weakNerveEdges (cofibrantAlgebraRelativeCategory A)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.isLocalization_of_rightKan_local_limits
    (hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A))
    (weakNerveEdges (cofibrantAlgebraRelativeCategory A))
    (hammockLocalizationNerveMap_inverts (cofibrantAlgebraRelativeCategory A))
  · intro E _ G
    exact cofibrantSourceRightKanExtension_refl A G
  · intro E _ F hF z
    exact cofibrantSourceRightKanDiagram_hasLimit_all A F hF z
  · intro E _ F hF G α hα x
    exact cofibrantSourceRightKanUnit_isInvertible A F hF G α hα x

lemma cAlgLocalizationSource_isLocalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (cAlgLocalizationSource A)
      (weakNerveEdges (cofibrantAlgebraRelativeCategory A)) :=
  (cAlgLocalizationSource_isLocalization_iff A).mpr
    (cofibrantHammockLocalization_isLocalization A)

lemma cAlgLocalizationPrecomposition_isQCatEquivalence
    (E : SSet.{u + 1}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (cAlgLocalizationSource A)
      (weakNerveEdges (cofibrantAlgebraRelativeCategory A))
      (cAlgLocalizationSource_inverts A) E) := by
  obtain ⟨h, he⟩ := cAlgLocalizationSource_isLocalization A
  exact he E

end SerrePositivity.EInfinity.BarrattEccles
