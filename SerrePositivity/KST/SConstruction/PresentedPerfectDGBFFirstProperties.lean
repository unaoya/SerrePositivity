module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFFirstStage

/-! # 最初の実 BF 段の Kan 性・単射性・元の評価の回収
概要：元の零段 ΩB₀ を保持し、K₁ は Kan、最初の構造射は単射、B₀ 比較は anodyne。
方針：同じ評価への一般の Kan 単射置換の証明済みの性質を適用する。
規約：Ω 条件と全帰納列の完成は別工程。使われ方：次の前向き帰納 span の基底。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 同じ元の B₀ は、既存の零次全境界商の同じ Ex∞ Kan 値。 -/
lemma presentedPerfectDGBFBaseFunctor_obj (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBFBaseFunctor A).obj C).obj =
      ((presentedPerfectDGBoundaryKanEnrichedFunctor A 0).obj C).obj := rfl

/-- 元の零段は、同じ零次全境界 Kan 商の loop 対象そのもの。 -/
lemma presentedPerfectDGBFZeroFunctor_obj (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBFZeroFunctor A).obj C).obj =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((presentedPerfectDGBoundaryKanEnrichedFunctor A 0).obj C).obj := rfl

/-- 同じ元の零段 ΩB₀ と全 Hom を、Kan 対象へ束ねる。 -/
def presentedPerfectDGBFZeroKanFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedKanObject.{max (u + 1) v} :=
  pointedEnrichedKanLift (presentedPerfectDGBFZeroFunctor A)
    (presentedPerfectDGBFZero_kanComplex A)

/-- 同じ最初の実 BF 段 K₁ は Kan 複体。 -/
instance presentedPerfectDGBFFirst_kanComplex (C : PerfDGInput.{u, v} A) :
    KanComplex (((presentedPerfectDGBFFirstFunctor A).obj C).obj).right :=
  pointedEnrichedMonicReplacement_kanComplex (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A) C

/-- 同じ最初の実構造射 ΣΩB₀→K₁ は基礎単射。 -/
lemma presentedPerfectDGBFFirstStructureMap_mono (C : PerfDGInput.{u, v} A) :
    Mono (show ((presentedPerfectDGBFZeroSuspensionFunctor A).obj C).obj ⟶
      ((presentedPerfectDGBFFirstFunctor A).obj C).obj from
        presentedPerfectDGBFFirstStructureMap A C).right :=
  pointedEnrichedMonicReplacementSource_mono (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A) C

/-- 同じ元の B₀ から最初の実段 K₁ への比較は基礎 anodyne 射。 -/
lemma presentedPerfectDGBFFirstComparison_anodyne (C : PerfDGInput.{u, v} A) :
    anodyneExtensions (show ((presentedPerfectDGBFBaseFunctor A).obj C).obj ⟶
      ((presentedPerfectDGBFFirstFunctor A).obj C).obj from
        presentedPerfectDGBFFirstComparison A C).right :=
  pointedEnrichedMonicReplacementTarget_anodyne (presentedPerfectDGBFZeroSuspensionFunctor A)
    (presentedPerfectDGBFBaseFunctor A) (presentedPerfectDGBFZeroEvaluation A)
    (presentedPerfectDGBFZeroEvaluation_whisker A) C

/-- 最初の構造射は、局所化で元の評価と同じ B₀ 比較の合成を回収する。 -/
lemma presentedPerfectDGBFFirstStructure_localized_eq (C : PerfDGInput.{u, v} A) :
    AnodyneHomotopy.anodyneQ.map
        (show ((presentedPerfectDGBFZeroSuspensionFunctor A).obj C).obj ⟶
          ((presentedPerfectDGBFFirstFunctor A).obj C).obj from
            presentedPerfectDGBFFirstStructureMap A C).right =
      AnodyneHomotopy.anodyneQ.map
          (show ((presentedPerfectDGBFZeroSuspensionFunctor A).obj C).obj ⟶
            ((presentedPerfectDGBFBaseFunctor A).obj C).obj from
              presentedPerfectDGBFZeroEvaluation A C).right ≫
        AnodyneHomotopy.anodyneQ.map
          (show ((presentedPerfectDGBFBaseFunctor A).obj C).obj ⟶
            ((presentedPerfectDGBFFirstFunctor A).obj C).obj from
              presentedPerfectDGBFFirstComparison A C).right :=
  pointedEnrichedMonicReplacementSource_localized_eq
    (presentedPerfectDGBFZeroSuspensionFunctor A) (presentedPerfectDGBFBaseFunctor A)
    (presentedPerfectDGBFZeroEvaluation A) (presentedPerfectDGBFZeroEvaluation_whisker A)
    AnodyneHomotopy.anodyneQ (Localization.inverts _ anodyneExtensions) C

/-- 最初の厳密豊穣構造変換は、同じ元の実構造射を成分に持つ。 -/
lemma presentedPerfectDGBFFirstStructureTransformation_app (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFFirstStructureTransformation A).app C =
      eHomEquiv SSet (presentedPerfectDGBFFirstStructureMap A C) := rfl

/-- 最初の厳密豊穣比較変換は、同じ元の B₀ 比較を成分に持つ。 -/
lemma presentedPerfectDGBFFirstComparisonTransformation_app (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFFirstComparisonTransformation A).app C =
      eHomEquiv SSet (presentedPerfectDGBFFirstComparison A C) := rfl

/-- 同じ元の B₀ 比較は、全基点・全次数の実際の π 同型。 -/
lemma presentedPerfectDGBFFirstComparison_piIsomorphism (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (show ((presentedPerfectDGBFBaseFunctor A).obj C).obj ⟶
        ((presentedPerfectDGBFFirstFunctor A).obj C).obj from
          presentedPerfectDGBFFirstComparison A C).right := by
  exact kanPiIsomorphism_of_anodyne _ (presentedPerfectDGBFFirstComparison_anodyne A C)

end SerrePositivity.KST.SConstruction
