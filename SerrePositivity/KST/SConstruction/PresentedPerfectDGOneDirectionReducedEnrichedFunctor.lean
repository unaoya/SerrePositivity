module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionReducedLaws
public import SerrePositivity.KST.SConstruction.InternalEnrichedActionFunctor

/-! # 元の一次方向の全零境界商の全 native 豊穣関手
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

/-- 同じ元の一次方向の全零境界商への、全 native Kan dg 入力族を保つ厳密豊穣関手。 -/
def presentedPerfectDGOneDirectionReducedEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SSetInternalObject.{max (u + 1) v} :=
  internalEnrichedFunctorOfAction
    (fun C => (oneDirectionReducedRealization r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right)
    (presentedPerfectDGOneDirectionReducedAction A r)
    (presentedPerfectDGOneDirectionReducedAction_unit A r)
    (presentedPerfectDGOneDirectionReducedAction_comp A r)

/-- 実値は同じ元の全零境界を潰す点つき商の基礎単体集合。 -/
lemma presentedPerfectDGOneDirectionReducedEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGOneDirectionReducedEnrichedFunctor A r).obj C).obj =
      (oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C))).right := rfl

/-- 全 Hom 作用は、元の同じ基点固定写像空間の全入力族を経由する。 -/
lemma presentedPerfectDGOneDirectionReducedEnrichedFunctor_family (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGOneDirectionReducedFamilyMap A r C D ≫
      PointedObject.basedHomι
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)))
        (oneDirectionReducedRealization r
          (stableCategoryModel (presentedPerfectDGStableCategory A D))) =
      (presentedPerfectDGOneDirectionReducedEnrichedFunctor A r).map C D :=
  presentedPerfectDGOneDirectionReducedFamilyMap_inclusion A r C D

/-- 元の通常 dg 入力射では、同じ元の点つき商射の基礎射を厳密に回収する。 -/
lemma presentedPerfectDGOneDirectionReducedEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGOneDirectionReducedEnrichedFunctor A r).map C D =
        curry' (C := SSet.{max (u + 1) v})
          (oneDirectionReducedRealizationMap r
            (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
              stableCategoryModel (presentedPerfectDGStableCategory A D) from
                ⟨(presentedPerfectDGExactMap A F).hom,
                  preservesCofiberData_of_isExactFunctor
                    (presentedPerfectDGExactMap A F).hom⟩)).right :=
  internalEnrichedFunctorOfAction_hom _ _ _ _ F _
    (presentedPerfectDGOneDirectionReducedAction_hom A r F)

end SerrePositivity.KST.SConstruction
