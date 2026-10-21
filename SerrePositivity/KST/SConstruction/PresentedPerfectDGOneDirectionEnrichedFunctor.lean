module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionObjectFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAssemblyAction

/-! # 一次方向の元の実現への厳密豊穣関手
概要：元の一次方向実現と全作用を同じ閉 Hom 値豊穣関手へ束ねる。
方針：元の図式値豊穣関手と元の対角豊穣関手を合成する。
規約：元の値・通常射・全パラメータを保持する。使われ方：同じ商の作用法則の反映。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 一次方向を固定した元の実現への、全 native 入力を保つ厳密豊穣関手。 -/
def presentedPerfectDGOneDirectionEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SSetInternalObject.{max (u + 1) v} :=
  (presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).comp SSet
    simplicialSSetDiagramDiagonalEnrichedFunctor

/-- 実値は、元の一次方向を固定した同じ実現。 -/
lemma presentedPerfectDGOneDirectionEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGOneDirectionEnrichedFunctor A r).obj C).obj =
      (oneDirectionRealizationFunctor r).obj
        (stableCategoryModel (presentedPerfectDGStableCategory A C)) := rfl

/-- 全 Hom の評価は、既存の同じ一次方向の全 native 作用。 -/
lemma presentedPerfectDGOneDirectionEnrichedFunctor_action (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    uncurry ((presentedPerfectDGOneDirectionEnrichedFunctor A r).map C D) =
      presentedPerfectDGOneDirectionAction A r C D := rfl

/-- 元の通常 dg 射では、同じ一次方向実現の元の射を回収する。 -/
lemma presentedPerfectDGOneDirectionEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGOneDirectionEnrichedFunctor A r).map C D =
        curry' (C := SSet.{max (u + 1) v}) ((oneDirectionRealizationFunctor r).map
          ⟨(presentedPerfectDGExactMap A F).hom,
            preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    ((presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).map C D ≫
      simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _)
      (presentedPerfectDGOneDirectionObjectEnrichedFunctor_hom A r F)).trans
        (simplicialSSetDiagramDiagonalEnrichedFunctor_hom
          (presentedPerfectDGOneDirectionObjectMap A r F)))

end SerrePositivity.KST.SConstruction
