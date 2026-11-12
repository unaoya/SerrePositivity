module

public import SerrePositivity.KST.Spectra.PointedTotalizationComparisonPi
public import SerrePositivity.KST.Spectra.PointedWeightedEndUnderlyingWeight

/-!
概要：通常の点つき Tot は標準単体の点つき enriched end と厳密に同型。
方針：基礎単体集合の二つの end の同型を合成し、各射影で標準基点を比較する。
規約：Kan 性や Reedy 条件を要求しない。
使われ方：Goerss–Jardine VIII §1、HA §1.4.2。通常 Tot の Ω 構造と重み比較の接続。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet


namespace SerrePositivity.KST.Spectra.PointedTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 通常の点つき Tot と標準単体の点つき enriched end の同型。 -/
def standardEndIso (X : CosimplicialObject PointedSimplicialSet.{u}) :
    obj X ≅ PointedWeightedEnd.obj (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X) :=
  Under.isoMk
    (CosimplicialTotalization.smallEndIso (X ⋙ PointedSimplicialSet.forget) ≪≫
      (PointedWeightedEnd.underlyingIso (AsSmall.down ⋙ stdSimplex)
        (AsSmall.down ⋙ X)).symm) (by
    apply (cancel_mono (PointedWeightedEnd.underlyingIso
      (AsSmall.down ⋙ stdSimplex) (AsSmall.down ⋙ X)).hom).mp
    change ((obj X).hom ≫ (CosimplicialTotalization.smallEndIso _).hom ≫ _) ≫ _ = _
    rw [Category.assoc, Category.assoc]
    erw [Iso.inv_hom_id]
    rw [Category.comp_id, PointedWeightedEnd.underlyingIso_basepoint]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
    intro j
    change ((obj X).hom ≫ CosimplicialTotalization.toSmallEnd _) ≫ _ = _
    rw [Category.assoc]
    erw [CosimplicialTotalization.toSmallEnd_π (X ⋙ PointedSimplicialSet.forget) j]
    change CosimplicialTotalization.lift (basepointFamily X) ≫
      CosimplicialTotalization.π _ (AsSmall.down.obj j) = _
    rw [CosimplicialTotalization.lift_π, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_π]
    rfl)

/-- 同型の基礎射は構成済みの二つの end の同型の合成。 -/
@[reassoc]
lemma standardEndIso_underlying (X : CosimplicialObject PointedSimplicialSet.{u}) :
    (standardEndIso X).hom.right ≫
      (PointedWeightedEnd.underlyingIso (AsSmall.down ⋙ stdSimplex)
        (AsSmall.down ⋙ X)).hom =
    (CosimplicialTotalization.smallEndIso (X ⋙ PointedSimplicialSet.forget)).hom := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc]
  erw [Iso.inv_hom_id]
  rw [Category.comp_id]

/-- 通常の点つき Tot 比較も標準同型と重みの前合成の合成そのもの。 -/
lemma weightedEndComparison_eq_preMap (X : CosimplicialObject PointedSimplicialSet.{u}) :
    weightedEndComparison X = (standardEndIso X).hom ≫
      PointedWeightedEnd.preMap CosimplicialLastVertex.weightMap (AsSmall.down ⋙ X) := by
  apply Under.UnderMorphism.ext
  apply (cancel_mono (PointedWeightedEnd.underlyingIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X)).hom).mp
  change (weightedEndComparison X).right ≫ _ =
    ((standardEndIso X).hom.right ≫
      (PointedWeightedEnd.preMap _ _).right) ≫ _
  rw [weightedEndComparison_underlying, Category.assoc,
    PointedWeightedEnd.underlyingIso_preMap, ← Category.assoc, standardEndIso_underlying]
  exact CosimplicialTotalization.bousfieldKanComparison_eq_weightedPre
    (X ⋙ PointedSimplicialSet.forget)

end
end SerrePositivity.KST.Spectra.PointedTotalization
