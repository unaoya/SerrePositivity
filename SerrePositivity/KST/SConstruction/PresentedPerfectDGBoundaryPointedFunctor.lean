module
public import SerrePositivity.KST.SConstruction.PointedEnrichedActionFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryReducedEnrichedFunctor

/-! # 元の境界商への標準点つき厳密豊穣関手
概要：同じ境界商と全 native basedHom 族を、標準の点つき豊穣関手へ束ねる。
方針：包含後に検証済みの単位・合成を標準 basedHom に反映する。
規約：元の点つき値・通常射を変更しない。使われ方：点つき Kan 置換と BF K。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の同じ点つき境界商を標準の点つき対象として保持する。 -/
def presentedPerfectDGBoundaryPointedObject (r : ℕ) (C : PerfDGInput.{u, v} A) :
    PointedSSetObject.{max (u + 1) v} :=
  ⟨boundaryReducedRealization r (stableCategoryModel (presentedPerfectDGStableCategory A C))⟩

/-- 元の同じ点つき商と全 native 入力族を持つ、標準の厳密点つき豊穣関手。 -/
def presentedPerfectDGBoundaryPointedEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  pointedEnrichedFunctorOfAction (presentedPerfectDGBoundaryPointedObject A r)
    (presentedPerfectDGBoundaryReducedAction A r)
    (presentedPerfectDGBoundaryReducedAction_unit A r)
    (presentedPerfectDGBoundaryReducedAction_comp A r)
    (presentedPerfectDGBoundaryReducedFamilyMap A r)
    (presentedPerfectDGBoundaryReducedFamilyMap_inclusion A r)

/-- 標準点つき関手の実値は、同じ元の点つき境界商。 -/
lemma presentedPerfectDGBoundaryPointedEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C).obj =
      boundaryReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory A C)) := rfl

/-- 標準 basedHom への作用は、同じ元の全 native 基点固定写像族。 -/
lemma presentedPerfectDGBoundaryPointedEnrichedFunctor_map (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).map C D =
      presentedPerfectDGBoundaryReducedFamilyMap A r C D := rfl

/-- 通常の厳密 dg 入力射は、同じ元の点つき境界商の射として回収される。 -/
lemma presentedPerfectDGBoundaryPointedEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).map C D =
        eHomEquiv SSet.{max (u + 1) v}
          (show (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj C ⟶
            (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).obj D from
            boundaryReducedRealizationMap r
              (show stableCategoryModel (presentedPerfectDGStableCategory A C) ⟶
                stableCategoryModel (presentedPerfectDGStableCategory A D) from
                  ⟨(presentedPerfectDGExactMap A F).hom,
                    preservesCofiberData_of_isExactFunctor
                      (presentedPerfectDGExactMap A F).hom⟩)) :=
  pointedEnrichedFunctorOfAction_hom _ _ _ _ _ _ F _
    (presentedPerfectDGBoundaryReducedAction_hom A r F)

/-- 基礎単体集合へ忘れると、供給済みの同じ元の閉 Hom 値豊穣関手になる。 -/
lemma presentedPerfectDGBoundaryPointedEnrichedFunctor_forget (r : ℕ) :
    (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).comp SSet
      pointedSSetObjectClosedForget = presentedPerfectDGBoundaryReducedEnrichedFunctor A r := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) ?_
  intro C D
  exact (Category.comp_id _).trans
    (presentedPerfectDGBoundaryReducedEnrichedFunctor_family A r C D)

end SerrePositivity.KST.SConstruction
