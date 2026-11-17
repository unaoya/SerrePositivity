module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockSourceFunctor
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanComparisonNerves
public import SerrePositivity.EInfinity.Hammock.ExInfinityEnrichedUnit
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
# 元の通常圏から実 Kan hammock nerve への関手

概要：元の通常関手を同じ Ex∞ 単位と既存の nerveToCoherent で送る。
方針：通常関手の全単体への nerve と元の単体的圏の比較を合成する。
規約：元の通常圏・同じ射・同じ頂点を保持する。
使われ方：元の実 DK nerve への局所化関手の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.EInfinity.Hammock _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

def kanHammockSourceFunctor : C.category ⥤ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C ⋙ (exInfinityEnrichedUnit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C)).forget

lemma kanHammockSourceFunctor_homTo {X Y : C.category} (f : X ⟶ Y) :
    ForgetEnrichment.homTo SSet.{u} ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph C.weakEquivalences X Y) := by
  change ForgetEnrichment.homTo SSet.{u}
    (ForgetEnrichment.homOf SSet.{u} (ForgetEnrichment.homTo SSet.{u}
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor C).map f) ≫
        (exInfinityEnrichedUnit (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.HammockObjects C)).map X Y)) = _
  rw [ForgetEnrichment.homTo_homOf, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockSourceFunctor_homTo]
  rfl

def hammockLocalizationNerveMap : nerve C.category ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve C :=
  nerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C)

lemma hammockLocalizationNerveMap_vertex (X : C.category) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).obj X) := by
  change ((nerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C)).app (Opposite.op ⦋0⦌)) _ = _
  rw [NatTrans.comp_app_apply, nerveMap_app_mk₀]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent_vertex _

lemma hammockLocalizationNerveMap_arrow {X Y : C.category} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C)).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C).map f)) := by
  change ((nerveMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockSourceFunctor C) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.KanHammockCategory C)).app (Opposite.op ⦋1⦌)) _ = _
  rw [NatTrans.comp_app_apply, nerveMap_app_mk₁]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
