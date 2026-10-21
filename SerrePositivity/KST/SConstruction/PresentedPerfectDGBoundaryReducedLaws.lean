module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryReducedAction

/-! # 同じ元の点つき境界商の全作用の法則
概要：元の境界商上の全 native 作用は、単位・合成を厳密に保ち元の通常射を回収する。
方針：実現作用の同じ法則を、商の pushout の二脚で反映する一般補題へ渡す。
規約：基点の選択を変更しない。使われ方：点つき Kan 置換と厳密豊穣 K。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全 native 恒等入力は、同じ境界商上の厳密な恒等作用。 -/
lemma presentedPerfectDGBoundaryReducedAction_unit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (𝟙 (boundaryReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right ⊗ₘ
        eId SSet.{max (u + 1) v} C) ≫ presentedPerfectDGBoundaryReducedAction A r C C =
      (ρ_ (boundaryReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right).hom :=
  cofiberFamilyAction_unit _ _ _ (presentedPerfectDGBoundaryReducedAction_collapse A r C C)
    (presentedPerfectDGMultiRealizationAction_unit A (r + 1) C)

/-- 二回の元の商作用は、同じ native dg 合成による作用と全単体で厳密に一致。 -/
lemma presentedPerfectDGBoundaryReducedAction_comp (r : ℕ) (C D E : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBoundaryReducedAction A r C D ⊗ₘ
      𝟙 (D ⟶[SSet.{max (u + 1) v}] E)) ≫ presentedPerfectDGBoundaryReducedAction A r D E =
      (α_ (boundaryReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right
        (C ⟶[SSet.{max (u + 1) v}] D) (D ⟶[SSet.{max (u + 1) v}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{max (u + 1) v} C D E) ≫
            presentedPerfectDGBoundaryReducedAction A r C E :=
  cofiberFamilyAction_comp
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).ι
    (zeroDirectionsFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A E))).ι
    (presentedPerfectDGMultiRealizationAction A (r + 1) C D)
    (presentedPerfectDGMultiRealizationAction A (r + 1) D E)
    (presentedPerfectDGMultiRealizationAction A (r + 1) C E)
    (eComp SSet.{max (u + 1) v} C D E)
    (presentedPerfectDGBoundaryReducedAction_collapse A r C D)
    (presentedPerfectDGBoundaryReducedAction_collapse A r D E)
    (presentedPerfectDGBoundaryReducedAction_collapse A r C E)
    (presentedPerfectDGMultiRealizationAction_comp A (r + 1) C D E)

/-- 通常 dg 入力射では、同じ元の基点付き境界商の射を全作用から回収する。 -/
lemma presentedPerfectDGBoundaryReducedAction_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (𝟙 (boundaryReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right ⊗ₘ
        eHomEquiv SSet.{max (u + 1) v} F) ≫ presentedPerfectDGBoundaryReducedAction A r C D =
      (ρ_ (boundaryReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right).hom ≫
          (boundaryReducedRealizationMap r
            (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
              stableCategoryModel (presentedPerfectDGStableCategory A D) from
                ⟨(presentedPerfectDGExactMap A F).hom,
                  preservesCofiberData_of_isExactFunctor
                    (presentedPerfectDGExactMap A F).hom⟩)).right :=
  cofiberFamilyAction_hom _ _ _ _ (presentedPerfectDGBoundaryReducedAction_collapse A r C D)
    _ (boundaryReducedRealizationMap r _)
    (presentedPerfectDGMultiRealizationAction_hom A (r + 1) F)
    (boundaryReducedRealizationMap_quotient r _)

end SerrePositivity.KST.SConstruction
