module

public import SerrePositivity.EInfinity.SimplicialLocalization.HammockSourceFunctor
public import SerrePositivity.EInfinity.SimplicialLocalization.KanComparisonNerves
public import SerrePositivity.EInfinity.Hammock.ExInfinityEnrichedUnit
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderDiagrams

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock SerrePositivity.InfinityCategories SerrePositivity.KST.Comparison
open scoped Simplicial
variable (C : RelativeCategory.{u})

def kanHammockSourceFunctor : C.category ⥤ KanHammockCategory C :=
  hammockSourceFunctor C ⋙ (exInfinityEnrichedUnit (HammockObjects C)).forget

lemma kanHammockSourceFunctor_homTo {X Y : C.category} (f : X ⟶ Y) :
    ForgetEnrichment.homTo SSet.{u} ((kanHammockSourceFunctor C).map f) =
      arrowMap C.weakEquivalences f ≫
        exInfinityUnit.app (colimitGraph C.weakEquivalences X Y) := by
  change ForgetEnrichment.homTo SSet.{u}
    (ForgetEnrichment.homOf SSet.{u} (ForgetEnrichment.homTo SSet.{u}
      ((hammockSourceFunctor C).map f) ≫
        (exInfinityEnrichedUnit (HammockObjects C)).map X Y)) = _
  rw [ForgetEnrichment.homTo_homOf, hammockSourceFunctor_homTo]
  rfl

def hammockLocalizationNerveMap : nerve C.category ⟶ kanHammockNerve C :=
  nerveMap (kanHammockSourceFunctor C) ≫ nerveToCoherent (KanHammockCategory C)

lemma hammockLocalizationNerveMap_vertex (X : C.category) :
    (hammockLocalizationNerveMap C).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X) =
      coherentNerveVertex ((kanHammockSourceFunctor C).obj X) := by
  change ((nerveMap (kanHammockSourceFunctor C) ≫
    nerveToCoherent (KanHammockCategory C)).app (Opposite.op ⦋0⦌)) _ = _
  rw [NatTrans.comp_app_apply, nerveMap_app_mk₀]
  exact nerveToCoherent_vertex _

lemma hammockLocalizationNerveMap_arrow {X Y : C.category} (f : X ⟶ Y) :
    (hammockLocalizationNerveMap C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) =
      (nerveToCoherent (KanHammockCategory C)).app (Opposite.op ⦋1⦌)
        (ComposableArrows.mk₁ ((kanHammockSourceFunctor C).map f)) := by
  change ((nerveMap (kanHammockSourceFunctor C) ≫
    nerveToCoherent (KanHammockCategory C)).app (Opposite.op ⦋1⦌)) _ = _
  rw [NatTrans.comp_app_apply, nerveMap_app_mk₁]

end SerrePositivity.EInfinity.SimplicialLocalization
