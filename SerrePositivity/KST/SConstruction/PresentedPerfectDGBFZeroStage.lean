module
public import SerrePositivity.KST.SConstruction.PointedStandardLoopEvaluation
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBoundaryKanFunctor
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-! # 厳密 dg 入力における元の ΩB₀ と評価
概要：元の零次境界商の Ex∞ を B₀ とし、零段 ΩB₀ と評価 ΣΩB₀→B₀ を構成する。
方針：同じ標準点つき loop と tensor の厳密豊穣関手を合成する。
規約：B₀ 自体を零段にしない。使われ方：BF の最初の関手的単射置換。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 同じ元の零次境界商の Ex∞ Kan 値 B₀ を持つ標準点つき豊穣関手。 -/
def presentedPerfectDGBFBaseFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGBoundaryPointedEnrichedFunctor A 0).comp SSet
    exInfinityPointedEnrichedFunctor

/-- 同じ元の B₀ の基礎単体集合は Ex∞ Kan 複体。 -/
instance presentedPerfectDGBFBase_kanComplex (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFBaseFunctor A).obj C).obj).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _

/-- BF の零段は、同じ元の B₀ の loop 対象 ΩB₀。 -/
def presentedPerfectDGBFZeroFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGBFBaseFunctor A).comp SSet pointedStandardLoopEnrichedFunctor

/-- 同じ元の零段の suspension ΣΩB₀。 -/
def presentedPerfectDGBFZeroSuspensionFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  (presentedPerfectDGBFZeroFunctor A).comp SSet
    (pointedTensorEnrichedFunctor PointedSimplicialSet.circle)

/-- 同じ B₀ 上の元の評価 ΣΩB₀→B₀。 -/
def presentedPerfectDGBFZeroEvaluation (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFZeroSuspensionFunctor A).obj C ⟶
      (presentedPerfectDGBFBaseFunctor A).obj C :=
  pointedStandardLoopEvaluation ((presentedPerfectDGBFBaseFunctor A).obj C)

/-- 元の同じ評価は、全厳密 dg 入力 Hom に厳密に自然。 -/
lemma presentedPerfectDGBFZeroEvaluation_whisker (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFZeroSuspensionFunctor A).map C D ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGBFZeroSuspensionFunctor A).obj C)
          (presentedPerfectDGBFZeroEvaluation A D) =
      (presentedPerfectDGBFBaseFunctor A).map C D ≫
        eHomWhiskerRight SSet (presentedPerfectDGBFZeroEvaluation A C)
          ((presentedPerfectDGBFBaseFunctor A).obj D) := by
  have h := congrArg (fun q => (presentedPerfectDGBFBaseFunctor A).map C D ≫ q)
    (pointedStandardLoopEvaluation_whisker
      ((presentedPerfectDGBFBaseFunctor A).obj C) ((presentedPerfectDGBFBaseFunctor A).obj D))
  change (((presentedPerfectDGBFBaseFunctor A).map C D ≫
    pointedStandardLoopEnrichedFunctor.map _ _) ≫
      (pointedTensorEnrichedFunctor PointedSimplicialSet.circle).map _ _) ≫ _ = _
  erw [Category.assoc, Category.assoc]
  exact (congrArg (fun q => (presentedPerfectDGBFBaseFunctor A).map C D ≫ q)
    (Category.assoc _ _ _)).symm.trans h

/-- 同じ元の評価を成分とする厳密豊穣自然変換。 -/
def presentedPerfectDGBFZeroEvaluationTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGBFZeroSuspensionFunctor A) (presentedPerfectDGBFBaseFunctor A) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A)

/-- 零段の同じ元の値は Kan 複体。 -/
lemma presentedPerfectDGBFZero_kanComplex (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFZeroFunctor A).obj C).obj).right := by
  let _ : KanComplex (((presentedPerfectDGBFBaseFunctor A).obj C).obj).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  exact loopSpace_kanComplex _

end SerrePositivity.KST.SConstruction
