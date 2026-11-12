module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiRealizationEnrichedFunctor
public import SerrePositivity.KST.SConstruction.StableMultiRealizationEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEnrichedExactFunctor
public import SerrePositivity.KST.Fibration.CoreEnrichedPrecompose

/-! # 元の全反復 core S• 実現と、同じ ν の全 Hom の照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- 元の全多次数の core 作用は、ν の同じ全 Hom と安定側の作用の合成。 -/
theorem dgNuMultiSCore_map (r : ℕ) (d : Fin r → SimplexCategoryᵒᵖ)
    (P Q : PerfDGInput.{u, v} A) :
    (presentedPerfectDGEnrichedExactFunctor A).map P Q ≫
      ((stableMultiSCoreEnrichedDiagram r).obj d).map
        (presentedPerfectDGStableQCat A P) (presentedPerfectDGStableQCat A Q) =
      ((presentedPerfectDGMultiSCoreEnrichedDiagram A r).obj d).map P Q := by
  let E := presentedPerfectDGEnrichedExactFunctor A
  let I := coreEnrichedInclusion _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v}
  let F : EnrichedFunctor SSet.{max (u + 1) v}
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{max (u + 1) v} :=
    (multiSQuasicategoryEnrichedDiagram r).obj d
  change E.map P Q ≫ ((quasicategoryEnrichedCoreFunctor (I.comp SSet F)).map
    (E.obj P) (E.obj Q) ≫ 𝟙 _) =
    (quasicategoryEnrichedCoreFunctor ((E.comp SSet I).comp SSet F)).map P Q ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id]
  exact coreEnrichedPrecompose_assoc_map E I F P Q

/-- 元の反復 core S• 対角図式の全 Hom を、同じ ν の後で厳密に回収する。 -/
theorem dgNuMultiSCoreObject_map (r : ℕ) (P Q : PerfDGInput.{u, v} A) :
    (presentedPerfectDGEnrichedExactFunctor A).map P Q ≫
      (stableMultiSCoreObjectEnrichedFunctor r).map
        (presentedPerfectDGStableQCat A P) (presentedPerfectDGStableQCat A Q) =
      (presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).map P Q := by
  apply simplicialSSetDiagramHom_ext
  intro n
  have hl := stableMultiSCoreObjectEnrichedFunctor_projection r
    (presentedPerfectDGStableQCat A P) (presentedPerfectDGStableQCat A Q) n
  have hr := presentedPerfectDGMultiSCoreObjectEnrichedFunctor_projection A r P Q n
  exact (Category.assoc _ _ _).trans
    ((congrArg ((presentedPerfectDGEnrichedExactFunctor A).map P Q ≫ ·) hl).trans
      ((dgNuMultiSCore_map A r (fun _ => n) P Q).trans hr.symm))

/-- 元の対角実現の全 Hom 作用も、同じ ν と安定側実現の合成に厳密一致。 -/
theorem dgNuMultiRealization_map (r : ℕ) (P Q : PerfDGInput.{u, v} A) :
    (presentedPerfectDGEnrichedExactFunctor A).map P Q ≫
      (stableMultiRealizationEnrichedFunctor r).map
        (presentedPerfectDGStableQCat A P) (presentedPerfectDGStableQCat A Q) =
      (presentedPerfectDGMultiRealizationEnrichedFunctor A r).map P Q := by
  change _ ≫ (_ ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _) =
    _ ≫ simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _
  rw [← Category.assoc, dgNuMultiSCoreObject_map]

end SerrePositivity.KST.Fibration
