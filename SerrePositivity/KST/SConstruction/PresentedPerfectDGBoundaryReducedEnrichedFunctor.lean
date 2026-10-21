module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryReducedLaws
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionFunctor

/-! # 元の全零境界商の全 native 豊穣関手
概要：元の商上の全作用を束ね、元の basedHom を経由する厳密豊穣関手を与える。
方針：全作用の単位・合成と元の通常射の回収を、同じ閉内部 Hom で包装する。
規約：点つき商の基点と値を変えない。使われ方：点つき Kan 置換の厳密豊穣入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の全零境界商への、全 native Kan dg 入力族を保つ厳密豊穣関手。 -/
def presentedPerfectDGBoundaryReducedEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SSetInternalObject.{max (u + 1) v} :=
  internalEnrichedFunctorOfAction
    (fun C => (boundaryReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right)
    (presentedPerfectDGBoundaryReducedAction A r)
    (presentedPerfectDGBoundaryReducedAction_unit A r)
    (presentedPerfectDGBoundaryReducedAction_comp A r)

/-- 実値は同じ元の全零境界を潰す点つき商の基礎単体集合。 -/
lemma presentedPerfectDGBoundaryReducedEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBoundaryReducedEnrichedFunctor A r).obj C).obj =
      (boundaryReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right := rfl

/-- 全 Hom 作用は、元の同じ基点固定写像空間の全入力族を経由する。 -/
lemma presentedPerfectDGBoundaryReducedEnrichedFunctor_family (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGBoundaryReducedFamilyMap A r C D ≫
      PointedObject.basedHomι
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (boundaryReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D))) =
      (presentedPerfectDGBoundaryReducedEnrichedFunctor A r).map C D :=
  presentedPerfectDGBoundaryReducedFamilyMap_inclusion A r C D

/-- 元の通常 dg 入力射では、同じ元の点つき商射の基礎射を厳密に回収する。 -/
lemma presentedPerfectDGBoundaryReducedEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGBoundaryReducedEnrichedFunctor A r).map C D =
        curry' (C := SSet.{max (u + 1) v})
          (boundaryReducedRealizationMap r
            (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
              stableCategoryModel (presentedPerfectDGStableCategory A D) from
                ⟨(presentedPerfectDGExactMap A F).hom,
                  preservesCofiberData_of_isExactFunctor
                    (presentedPerfectDGExactMap A F).hom⟩)).right :=
  internalEnrichedFunctorOfAction_hom _ _ _ _ F _
    (presentedPerfectDGBoundaryReducedAction_hom A r F)

end SerrePositivity.KST.SConstruction
