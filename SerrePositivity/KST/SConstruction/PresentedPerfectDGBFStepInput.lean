module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblySpan
public import SerrePositivity.KST.SConstruction.PointedTensorComparison
public import SerrePositivity.KST.SConstruction.EnrichedWhiskerNaturality

/-! # 実際の BF 帰納段への元の前向き左脚
概要：元の Bᵣ→K の比較を suspension し、元の ΣUᵣ→ΣBᵣ の後に合成する。
方針：同じ通常成分と全 Hom 自然性を保ち、合成の括弧付けだけを照合する。
規約：入力の比較は前向きのまま。使われ方：正の BF 帰納 span の左標的 ΣK。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の同じ r 次境界商の Ex∞ Kan 値を持つ標準点つき豊穣関手。 -/
def presentedPerfectDGBFBoundaryFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGBoundaryPointedEnrichedFunctor A r).comp SSet
    exInfinityPointedEnrichedFunctor

variable (r : ℕ)
  (K : EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
    PointedSSetObject.{max (u + 1) v})
  (c : ∀ X, (presentedPerfectDGBFBoundaryFunctor A r).obj X ⟶ K.obj X)
  (hc : ∀ X Y, (presentedPerfectDGBFBoundaryFunctor A r).map X Y ≫
      eHomWhiskerLeft SSet ((presentedPerfectDGBFBoundaryFunctor A r).obj X) (c Y) =
    K.map X Y ≫ eHomWhiskerRight SSet (c X) (K.obj Y))

/-- 実際の既存の BF 段 K の suspension を持つ厳密豊穣関手。 -/
def presentedPerfectDGBFStepLeftTargetFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  K.comp SSet (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})

/-- 元の ΣBᵣ から実際の ΣK への、同じ前向き比較。 -/
def presentedPerfectDGBFStepSuspensionComparison (X : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj X ⟶
      (presentedPerfectDGBFStepLeftTargetFunctor A K).obj X :=
  PointedSimplicialSet.circle.{max (u + 1) v} ◁
    (show ((presentedPerfectDGBFBoundaryFunctor A r).obj X).obj ⟶ (K.obj X).obj from c X)

include hc in
/-- 元の ΣBᵣ から実際の ΣK への比較は全 Hom に厳密に自然。 -/
lemma presentedPerfectDGBFStepSuspensionComparison_whisker (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj X)
          (presentedPerfectDGBFStepSuspensionComparison A r K c Y) =
      (presentedPerfectDGBFStepLeftTargetFunctor A K).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGBFStepSuspensionComparison A r K c X)
          ((presentedPerfectDGBFStepLeftTargetFunctor A K).obj Y) := by
  have h := pointedTensorComparison_whisker PointedSimplicialSet.circle.{max (u + 1) v}
    (presentedPerfectDGBFBoundaryFunctor A r) K c hc X Y
  change (((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).map X Y ≫
    exInfinityPointedEnrichedFunctor.map _ _) ≫
      (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map _ _) ≫
        _ = _ at h
  change ((presentedPerfectDGBoundaryPointedEnrichedFunctor A r).map X Y ≫
    (exInfinityPointedEnrichedFunctor.map _ _ ≫
      (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v}).map _ _)) ≫ _ = _
  erw [← Category.assoc]
  exact h

/-- 元の左脚の後に、同じ比較の suspension を合成した実左脚。 -/
def presentedPerfectDGBFStepLeftMap (X : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).obj X ⟶
      (presentedPerfectDGBFStepLeftTargetFunctor A K).obj X :=
  presentedPerfectDGKanAssemblyLeftMap A r X ≫
    presentedPerfectDGBFStepSuspensionComparison A r K c X

include hc in
/-- 実際の BF 帰納段への同じ合成左脚は全 Hom に自然。 -/
lemma presentedPerfectDGBFStepLeft_whisker (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblySourceFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblySourceFunctor A r).obj X)
          (presentedPerfectDGBFStepLeftMap A r K c Y) =
      (presentedPerfectDGBFStepLeftTargetFunctor A K).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGBFStepLeftMap A r K c X)
          ((presentedPerfectDGBFStepLeftTargetFunctor A K).obj Y) :=
  enriched_whisker_naturality_comp SSet
    ((presentedPerfectDGKanAssemblySourceFunctor A r).map X Y)
    ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map X Y)
    ((presentedPerfectDGBFStepLeftTargetFunctor A K).map X Y)
    (presentedPerfectDGKanAssemblyLeftMap A r X) (presentedPerfectDGKanAssemblyLeftMap A r Y)
    (presentedPerfectDGBFStepSuspensionComparison A r K c X)
    (presentedPerfectDGBFStepSuspensionComparison A r K c Y)
    (presentedPerfectDGKanAssemblyLeft_whisker A r X Y)
    (presentedPerfectDGBFStepSuspensionComparison_whisker A r K c hc X Y)

end SerrePositivity.KST.SConstruction
