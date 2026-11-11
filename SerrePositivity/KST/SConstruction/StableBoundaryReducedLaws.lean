module
public import SerrePositivity.KST.SConstruction.StableBoundaryReducedAction

/-! # 同じ元の点つき境界商の全作用の法則
概要：元の境界商上の完全関手の全作用は、単位・合成を厳密に保ち元の通常射を回収する。
方針：実現作用の同じ法則を、商の pushout の二脚で反映する一般補題へ渡す。
規約：基点の選択を変更しない。使われ方：点つき Kan 置換と厳密豊穣 K。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の完全関手の恒等入力は、同じ境界商上の厳密な恒等作用。 -/
lemma stableBoundaryReducedAction_unit (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (𝟙 (boundaryReducedRealization r
      (stableCategoryModel C)).right ⊗ₘ
        eId SSet.{u} C) ≫ stableBoundaryReducedAction r C C =
      (ρ_ (boundaryReducedRealization r
        (stableCategoryModel C)).right).hom :=
  cofiberFamilyAction_unit _ _ _ (stableBoundaryReducedAction_collapse r C C)
    (stableMultiRealizationAction_unit (r + 1) C)

/-- 二回の元の商作用は、同じ 完全関手 合成による作用と全単体で厳密に一致。 -/
lemma stableBoundaryReducedAction_comp (r : ℕ) (C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableBoundaryReducedAction r C D ⊗ₘ
      𝟙 (D ⟶[SSet.{u}] E)) ≫ stableBoundaryReducedAction r D E =
      (α_ (boundaryReducedRealization r
        (stableCategoryModel C)).right
        (C ⟶[SSet.{u}] D) (D ⟶[SSet.{u}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{u} C D E) ≫
            stableBoundaryReducedAction r C E :=
  cofiberFamilyAction_comp
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel C)).ι
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel D)).ι
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel E)).ι
    (stableMultiRealizationAction (r + 1) C D)
    (stableMultiRealizationAction (r + 1) D E)
    (stableMultiRealizationAction (r + 1) C E)
    (eComp SSet.{u} C D E)
    (stableBoundaryReducedAction_collapse r C D)
    (stableBoundaryReducedAction_collapse r D E)
    (stableBoundaryReducedAction_collapse r C E)
    (stableMultiRealizationAction_comp (r + 1) C D E)

/-- 元の通常完全射では、同じ点つき境界商の射を全作用から回収する。 -/
lemma stableBoundaryReducedAction_hom (r : ℕ) {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    (𝟙 (boundaryReducedRealization r (stableCategoryModel C)).right ⊗ₘ
        eHomEquiv SSet.{u} F) ≫ stableBoundaryReducedAction r C D =
      (ρ_ (boundaryReducedRealization r (stableCategoryModel C)).right).hom ≫
        (boundaryReducedRealizationMap r (stableExactInputMap F)).right :=
  cofiberFamilyAction_hom _ _ _ _ (stableBoundaryReducedAction_collapse r C D)
    _ (boundaryReducedRealizationMap r (stableExactInputMap F))
    (stableMultiRealizationAction_hom (r + 1) F)
    (boundaryReducedRealizationMap_quotient r _)

end SerrePositivity.KST.SConstruction
