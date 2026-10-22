module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStepInput
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderCompletionNaturality
public import SerrePositivity.KST.SConstruction.PointedEnrichedCylinderCompletionProperties

/-! # 実際の BF 帰納段への一般の円柱押し出しの適用
概要：元の Bᵣ→K の比較から、ΣK を左標的とする次の実 Kan 段を構成する。
方針：元の右脚と延長した左脚へ、同じ一般の実円柱押し出し＋Ex∞ を適用する。
規約：固定された元の ΣBᵣ を ΣK の代用にしない。使われ方：全正帰納列。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

variable (r : ℕ)
  (K : EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
    PointedSSetObject.{max (u + 1) v})
  (c : ∀ X, (presentedPerfectDGBFBoundaryFunctor A r).obj X ⟶ K.obj X)
  (hc : ∀ X Y, (presentedPerfectDGBFBoundaryFunctor A r).map X Y ≫
      eHomWhiskerLeft SSet ((presentedPerfectDGBFBoundaryFunctor A r).obj X) (c Y) =
    K.map X Y ≫ eHomWhiskerRight SSet (c X) (K.obj Y))

/-- 実際の ΣK を左標的とする次の同じ実 Kan 段の厳密豊穣関手。 -/
def presentedPerfectDGBFStepFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  pointedEnrichedCylinderCompletionFunctor (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r)

/-- 実際の ΣK を左標的とする次の同じ実 Kan 段の厳密豊穣関手。 -/
def presentedPerfectDGBFStepKanFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedKanObject.{max (u + 1) v} :=
  pointedEnrichedCylinderCompletionKanFunctor (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r)

/-- 同じ次の実 Kan 段への元の StructureMap の前向き成分。 -/
def presentedPerfectDGBFStepStructureMap (X : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFStepLeftTargetFunctor A K).obj X ⟶
      (presentedPerfectDGBFStepFunctor A r K c hc).obj X :=
  pointedEnrichedCylinderCompletionLeft (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X

/-- 同じ次の実 Kan 段への元の Comparison の前向き成分。 -/
def presentedPerfectDGBFStepComparison (X : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyTargetFunctor A r).obj X ⟶
      (presentedPerfectDGBFStepFunctor A r K c hc).obj X :=
  pointedEnrichedCylinderCompletionRight (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X

end SerrePositivity.KST.SConstruction
