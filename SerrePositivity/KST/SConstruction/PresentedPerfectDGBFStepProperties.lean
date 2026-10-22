module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStepValue

/-! # 実際の BF 帰納段の Kan 性・単射性・全 Hom 自然性
概要：実際の ΣK を左標的とする次段の値は Kan、構造射は単射で両比較は全 Hom に自然。
方針：同じ一般の実円柱押し出し＋Ex∞ の性質を元の実 span へ適用する。
規約：弱比較の保存は別に証明する。使われ方：全正 BF 帰納列の不変条件。
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

/-- 実際の次の BF 段は、同じ Ex∞ による Kan 複体。 -/
lemma presentedPerfectDGBFStep_kanComplex (X : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFStepFunctor A r K c hc).obj X).obj).right :=
  pointedEnrichedCylinderCompletion_kanComplex (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X

/-- 実際の ΣK から同じ次の実 Kan 段への構造射は基礎単射。 -/
lemma presentedPerfectDGBFStepStructureMap_mono (X : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGBFStepLeftTargetFunctor A K).obj X).obj ⟶
      ((presentedPerfectDGBFStepFunctor A r K c hc).obj X).obj from
        presentedPerfectDGBFStepStructureMap A r K c hc X).right :=
  pointedEnrichedCylinderCompletionLeft_mono (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X

/-- 同じ実 StructureMap 成分は、全厳密 dg 入力 Hom に自然。 -/
lemma presentedPerfectDGBFStepStructureMap_whisker (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFStepLeftTargetFunctor A K).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGBFStepLeftTargetFunctor A K).obj X)
        (presentedPerfectDGBFStepStructureMap A r K c hc Y) =
      (presentedPerfectDGBFStepFunctor A r K c hc).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGBFStepStructureMap A r K c hc X)
          ((presentedPerfectDGBFStepFunctor A r K c hc).obj Y) :=
  pointedEnrichedCylinderCompletionLeft_whisker (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X Y

/-- 同じ実 Comparison 成分は、全厳密 dg 入力 Hom に自然。 -/
lemma presentedPerfectDGBFStepComparison_whisker (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyTargetFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj X)
        (presentedPerfectDGBFStepComparison A r K c hc Y) =
      (presentedPerfectDGBFStepFunctor A r K c hc).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGBFStepComparison A r K c hc X)
          ((presentedPerfectDGBFStepFunctor A r K c hc).obj Y) :=
  pointedEnrichedCylinderCompletionRight_whisker (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGBFStepLeftTargetFunctor A K)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGBFStepLeftMap A r K c)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGBFStepLeft_whisker A r K c hc)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X Y

end SerrePositivity.KST.SConstruction
