module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFZeroStage
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacementProperties
public import SerrePositivity.KST.SConstruction.PointedEnrichedMonicReplacementTransformations

/-! # 同じ ΩB₀ の評価からの最初の関手的 BF 段
概要：元の評価 ΣΩB₀→B₀ を実写像円柱と Ex∞ で単射化する。
方針：同じ全 Hom 自然な評価へ一般の関手的 Kan 単射置換を適用する。
規約：零段 ΩB₀ を保持。使われ方：BF の最初の構造射と前向き B₀ 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の同じ零段評価から得られる最初の Kan BF 段 K₁。 -/
def presentedPerfectDGBFFirstFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  pointedEnrichedMonicReplacementFunctor (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A)

/-- 同じ最初の実 Kan 値と全 Hom を、Kan 対象へ束ねる。 -/
def presentedPerfectDGBFFirstKanFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedKanObject.{max (u + 1) v} :=
  pointedEnrichedMonicReplacementKanFunctor (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A)

/-- 元の最初の BF 構造射 ΣΩB₀→K₁ は、同じ実円柱の源比較。 -/
def presentedPerfectDGBFFirstStructureMap (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFZeroSuspensionFunctor A).obj C ⟶
      (presentedPerfectDGBFFirstFunctor A).obj C :=
  pointedEnrichedMonicReplacementSource (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A) C

/-- 元の同じ B₀ から最初の実 Kan 段 K₁ への前向き比較。 -/
def presentedPerfectDGBFFirstComparison (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFBaseFunctor A).obj C ⟶
      (presentedPerfectDGBFFirstFunctor A).obj C :=
  pointedEnrichedMonicReplacementTarget (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A) C

/-- 同じ最初の構造射を全 dg 入力上で保持する厳密豊穣変換。 -/
def presentedPerfectDGBFFirstStructureTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGBFZeroSuspensionFunctor A) (presentedPerfectDGBFFirstFunctor A) :=
  pointedEnrichedMonicReplacementSourceTransformation (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A)

/-- 同じ元の B₀ 比較を全 dg 入力上で保持する厳密豊穣変換。 -/
def presentedPerfectDGBFFirstComparisonTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{max (u + 1) v}))
      (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFFirstFunctor A) :=
  pointedEnrichedMonicReplacementTargetTransformation (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A)

end SerrePositivity.KST.SConstruction
