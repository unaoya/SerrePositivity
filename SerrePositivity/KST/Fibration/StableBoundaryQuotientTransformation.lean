module
public import SerrePositivity.KST.SConstruction.StableBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.StrictSimplicialTransformationComponent

/-! # 元の S• 実現から境界商への比較は、全完全関手族に対して自然 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 閉 Hom 値の同じ後合成は、内部 Hom 関手の作用そのもの。 -/
theorem internalObject_whiskerLeft (X : SSetInternalObject.{u})
    {Y Z : SSetInternalObject.{u}} (g : Y ⟶ Z) :
    eHomWhiskerLeft SSet X g = (ihom X.obj).map g := by
  change (ρ_ _).inv ≫ _ ◁ curry' (C := SSet.{u}) g ≫ MonoidalClosed.comp X.obj Y.obj Z.obj = _
  rw [whiskerLeft_curry'_comp, Iso.inv_hom_id_assoc]

/-- 閉 Hom 値の同じ前合成は、内部 Hom の前合成そのもの。 -/
theorem internalObject_whiskerRight {X Y : SSetInternalObject.{u}} (f : X ⟶ Y)
    (Z : SSetInternalObject.{u}) :
    eHomWhiskerRight SSet f Z = (pre (C := SSet.{u}) f).app Z.obj := by
  change (λ_ _).inv ≫ curry' (C := SSet.{u}) f ▷ _ ≫ MonoidalClosed.comp X.obj Y.obj Z.obj = _
  rw [curry'_whiskerRight_comp, Iso.inv_hom_id_assoc]

/-- 同じ境界商の基点を忘れ、元の全閉 Hom 作用を保持する。 -/
def stableBoundaryClosedEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} SSetInternalObject.{u} :=
  (stableBoundaryPointedEnrichedFunctor r).comp SSet pointedSSetObjectClosedForget

/-- 閉 Hom の包含後の同じ境界商族は、元の実作用の curry そのもの。 -/
theorem stableBoundaryClosedEnrichedFunctor_map (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableBoundaryClosedEnrichedFunctor r).map C D =
      curry (stableBoundaryReducedAction r C D) :=
  stableBoundaryReducedFamilyMap_inclusion r C D

/-- 元の商射は全 Hom の前後合成と可換である。 -/
theorem stableBoundaryQuotient_whisker (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableMultiRealizationEnrichedFunctor (r + 1)).map C D ≫
      eHomWhiskerLeft SSet ((stableMultiRealizationEnrichedFunctor (r + 1)).obj C)
        (show (stableMultiRealizationEnrichedFunctor (r + 1)).obj D ⟶
          (stableBoundaryClosedEnrichedFunctor r).obj D from
            boundaryReductionQuotient r (stableCategoryModel D)) =
    (stableBoundaryClosedEnrichedFunctor r).map C D ≫
      eHomWhiskerRight SSet
        (show (stableMultiRealizationEnrichedFunctor (r + 1)).obj C ⟶
          (stableBoundaryClosedEnrichedFunctor r).obj C from
            boundaryReductionQuotient r (stableCategoryModel C))
        ((stableBoundaryClosedEnrichedFunctor r).obj D) := by
  rw [internalObject_whiskerLeft, internalObject_whiskerRight]
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app,
    stableBoundaryClosedEnrichedFunctor_map, uncurry_curry]
  exact (stableBoundaryReducedAction_quotient r C D).symm

/-- 同じ元の商射を成分に持つ、全単体的な厳密豊穣自然変換。 -/
def stableBoundaryQuotientTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableMultiRealizationEnrichedFunctor (r + 1)) (stableBoundaryClosedEnrichedFunctor r) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _
    (fun C => boundaryReductionQuotient r (stableCategoryModel C))
    (stableBoundaryQuotient_whisker r)

end SerrePositivity.KST.Fibration
