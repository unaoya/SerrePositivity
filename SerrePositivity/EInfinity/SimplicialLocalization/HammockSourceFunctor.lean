module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ArrowMapComposition
public import SerrePositivity.EInfinity.SimplicialLocalization.ComparisonEnrichment
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# 元の通常圏から実 hammock 豊穣圏への関手

概要：元の任意の射を同じ一定単体の hammock 射へ送り、厳密な通常関手を得る。
方針：同じ arrowMap の恒等・合成保存と ForgetEnrichment の元の同値を使う。
規約：元の対象と元の通常の Category instance を保持する。
使われ方：元の通常圏から Kan hammock nerve への局所化関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

abbrev HammockCategory := ForgetEnrichment SSet.{u} (HammockObjects C)

def hammockSourceFunctor : C.category ⥤ HammockCategory C where
  obj X := ForgetEnrichment.of SSet.{u} (show HammockObjects C from X)
  map {X Y} f := ForgetEnrichment.homOf SSet.{u}
    (C := HammockObjects C) (X := X) (Y := Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f)
  map_id X := by
    change ForgetEnrichment.homOf SSet.{u} (C := HammockObjects C) (X := X) (Y := X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences (𝟙 X)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap_identity]
    exact ForgetEnrichment.homOf_eId SSet.{u} (show HammockObjects C from X)
  map_comp {X Y Z} f g := by
    have hc := ForgetEnrichment.homOf_comp SSet.{u}
      (C := HammockObjects C) (X := X) (Y := Y) (Z := Z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences g)
    exact (congrArg (ForgetEnrichment.homOf SSet.{u} (C := HammockObjects C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composeUnitMaps_arrowMap C.weakEquivalences f g)).symm.trans hc

lemma hammockSourceFunctor_homTo {X Y : C.category} (f : X ⟶ Y) :
    ForgetEnrichment.homTo SSet.{u} ((hammockSourceFunctor C).map f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap C.weakEquivalences f := ForgetEnrichment.homTo_homOf SSet.{u} _

end SerrePositivity.EInfinity.SimplicialLocalization
