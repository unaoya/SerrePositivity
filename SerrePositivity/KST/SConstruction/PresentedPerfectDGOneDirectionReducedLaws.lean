module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionReducedAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionActionLaws
public import SerrePositivity.KST.SConstruction.CofiberActionRecoveryLaws
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionReducedEvaluations

/-! # 同じ元の点つき境界商の全作用の法則
概要：元の一次方向の境界商上の全 native 作用は、単位・合成を厳密に保ち元の通常射を回収する。
方針：実現作用の同じ法則を、商の pushout の二脚で反映する一般補題へ渡す。
規約：基点の選択を変更しない。使われ方：点つき Kan 置換と厳密豊穣 K。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の全 native 恒等入力は、同じ境界商上の厳密な恒等作用。 -/
lemma presentedPerfectDGOneDirectionReducedAction_unit (r : ℕ) (C : PerfDGInput.{u, v} A) :
    (𝟙 (oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right ⊗ₘ
        eId SSet.{max (u + 1) v} C) ≫ presentedPerfectDGOneDirectionReducedAction A r C C =
      (ρ_ (oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right).hom :=
  cofiberFamilyAction_unit _ _ _ (presentedPerfectDGOneDirectionReducedAction_collapse A r C C)
    (presentedPerfectDGOneDirectionAction_unit A (r + 1) C)

/-- 二回の元の商作用は、同じ native dg 合成による作用と全単体で厳密に一致。 -/
lemma presentedPerfectDGOneDirectionReducedAction_comp (r : ℕ) (C D E : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionReducedAction A r C D ⊗ₘ
      𝟙 (D ⟶[SSet.{max (u + 1) v}] E)) ≫ presentedPerfectDGOneDirectionReducedAction A r D E =
      (α_ (oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right
        (C ⟶[SSet.{max (u + 1) v}] D) (D ⟶[SSet.{max (u + 1) v}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{max (u + 1) v} C D E) ≫
            presentedPerfectDGOneDirectionReducedAction A r C E :=
  cofiberAction_comp_of_app
    (P := C ⟶[SSet.{max (u + 1) v}] D)
    (R := D ⟶[SSet.{max (u + 1) v}] E)
    (S := C ⟶[SSet.{max (u + 1) v}] E)
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).ι
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A E))).ι
    (presentedPerfectDGOneDirectionReducedAction A r C D)
    (presentedPerfectDGOneDirectionReducedAction A r D E)
    (presentedPerfectDGOneDirectionReducedAction A r C E)
    (eComp SSet.{max (u + 1) v} C D E)
    (presentedPerfectDGOneDirectionReducedAction_comp_quotient_app A r C D E)
    (presentedPerfectDGOneDirectionReducedAction_comp_basepoint_app A r C D E)

/-- 通常 dg 入力射では、同じ元の基点付き境界商の射を全作用から回収する。 -/
lemma presentedPerfectDGOneDirectionReducedAction_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (𝟙 (oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right ⊗ₘ
        eHomEquiv SSet.{max (u + 1) v} F) ≫ presentedPerfectDGOneDirectionReducedAction A r C D =
      (ρ_ (oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right).hom ≫
          (oneDirectionReducedRealizationMap r
            (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
              stableCategoryModel (presentedPerfectDGStableCategory A D) from
                ⟨(presentedPerfectDGExactMap A F).hom,
                  preservesCofiberData_of_isExactFunctor
                    (presentedPerfectDGExactMap A F).hom⟩)).right :=
  cofiberAction_hom_of_app
    (P := C ⟶[SSet.{max (u + 1) v}] D)
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).ι
    (oneDirectionFatBoundary (r + 1)
      (stableCategoryModel (presentedPerfectDGStableCategory A D))).ι
    (presentedPerfectDGOneDirectionReducedAction A r C D)
    (eHomEquiv SSet.{max (u + 1) v} F) (presentedPerfectDGOneDirectionPointedMap A r F)
    (presentedPerfectDGOneDirectionReducedAction_hom_quotient_app A r F)
    (presentedPerfectDGOneDirectionReducedAction_hom_basepoint_app A r F)

end SerrePositivity.KST.SConstruction
