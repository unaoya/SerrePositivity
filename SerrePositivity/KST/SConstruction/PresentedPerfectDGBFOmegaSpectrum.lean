module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFSequence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFFirstOmega
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFStepOmega

/-! # 厳密 dg 入力から得る同じ実再帰 BF Ω スペクトル
概要：元の零段 ΩB₀ と全正再帰段を、同じ単射構造射の Ω スペクトルへ束ねる。
方針：実円柱の基点固定比較から証明した零段・正段の Ω 条件を適用する。
規約：全 Hom のスペクトル値豊穣関手化は別工程。使われ方：その実対象。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の実再帰 Kan 列は全ての構造随伴で Ω 条件を満たす。 -/
lemma presentedPerfectDGBFKanSequence_omegaCondition (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFKanSequence A C).OmegaCondition := by
  intro n
  cases n with
  | zero => exact presentedPerfectDGBFFirstStructureAdjoint_piIsomorphism A C
  | succ r =>
      exact presentedPerfectDGBFStepStructureAdjoint_piIsomorphism A r
        (presentedPerfectDGBFPositiveStage A r) C

/-- 同じ零段・全正段・単射構造射を保持する実際の BF Ω スペクトル。 -/
def presentedPerfectDGBFOmegaSpectrum (C : PerfDGInput.{u, v} A) :
    OmegaSpectrum.{max (u + 1) v} :=
  (presentedPerfectDGBFKanSequence A C).toOmegaSpectrum
    (fun n => presentedPerfectDGBFStructureMap_mono A n C)
    (presentedPerfectDGBFKanSequence_omegaCondition A C)

/-- 同じ実 BF Ω スペクトルの零段は元の零次境界 Kan 商の loop。 -/
lemma presentedPerfectDGBFOmegaSpectrum_zero (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGBFOmegaSpectrum A C).level 0).space =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((presentedPerfectDGBoundaryKanEnrichedFunctor A 0).obj C).obj := rfl

/-- 同じ実 BF Ω スペクトルの構造射は全て元の実再帰構造射。 -/
lemma presentedPerfectDGBFOmegaSpectrum_sigma (n : ℕ) (C : PerfDGInput.{u, v} A) :
    (presentedPerfectDGBFOmegaSpectrum A C).sigma n =
      (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (((presentedPerfectDGBFLevelFunctor A n).obj C).obj) ⟶
        ((presentedPerfectDGBFLevelFunctor A (n + 1)).obj C).obj from
          presentedPerfectDGBFStructureMap A n C) := rfl

end SerrePositivity.KST.SConstruction
