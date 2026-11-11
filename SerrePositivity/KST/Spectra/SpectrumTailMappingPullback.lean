module

public import SerrePositivity.KST.Spectra.SpectrumTailEnriched
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：一段移動の写像空間比較を零段の構造条件の厳密な引き戻しとして表示する。
方針：零段の写像と一段先の整合族を貼り、全評価によって普遍性を検査する。
規約：単体的な普遍性であり、π₀ のみの主張ではない。
使われ方：Ω 条件から一段移動の完全忠実性を証明するための引き戻し表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 一段先の整合族を、元の零段の構造射の境界で評価する。 -/
def tailMappingBoundary (X Y : OmegaSpectrum.{u}) : mappingSpace (tail X) (tail Y) ⟶
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level 0).space) (Y.level 1).space).right :=
  evaluation (tail X) (tail Y) 0 ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma 0) (Y.level 1).space

/-- 整合写像全体は、零段と残りの整合族を構造射の境界で貼った引き戻し。 -/
lemma tailMapping_isPullback (X Y : OmegaSpectrum.{u}) :
    IsPullback (evaluation X Y 0) (tailMapping X Y) (mappingStep X Y 0)
      (tailMappingBoundary X Y) := by
  apply IsPullback.mk'
  · rw [tailMappingBoundary, ← Category.assoc, tailMapping_evaluation]
    exact (evaluation_condition X Y 0).symm
  · intro T a b ha hb
    apply mapping_hom_ext
    intro n
    cases n with
    | zero => exact ha
    | succ n =>
      have h := congrArg (fun k ↦ k ≫ evaluation (tail X) (tail Y) n) hb
      simpa only [Category.assoc, tailMapping_evaluation] using h
  · intro T a b hab
    let f : ∀ n, T ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right :=
      fun n ↦ match n with
      | 0 => a
      | n + 1 => b ≫ evaluation (tail X) (tail Y) n
    have hf (n : ℕ) :
        f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
          f n ≫ mappingStep X Y n := by
      cases n with
      | zero => exact hab.symm
      | succ n =>
        change (b ≫ evaluation (tail X) (tail Y) (n + 1)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((tail X).sigma n) ((tail Y).level (n + 1)).space =
          (b ≫ evaluation (tail X) (tail Y) n) ≫ mappingStep (tail X) (tail Y) n
        rw [Category.assoc, evaluation_condition, ← Category.assoc]
    let l := TruncatedMapping.familyLift
      (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Y) f hf
    have hl (n : ℕ) : l ≫ evaluation X Y n = f n :=
      TruncatedMapping.familyLift_evaluation _ _ _ _ _ _ _ n
    refine ⟨l, hl 0, ?_⟩
    apply mapping_hom_ext
    intro n
    rw [Category.assoc, tailMapping_evaluation, hl]

/-- 写像空間の零段への評価は実際の Kan fibration。 -/
lemma evaluation_zero_fibration (X Y : OmegaSpectrum.{u}) : Fibration (evaluation X Y 0) := by
  let (n : ℕ) : Mono (X.sigma n).right := X.sigma_mono n
  have h := TruncatedMapping.total_projection_fibration
    (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (mappingStep X Y)
  change Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ 0 ≫ 𝟙 _)
  simpa only [Category.comp_id] using h

/-- 引き戻し表示の境界側は Kan fibration であり、右固有性を適用できる。 -/
lemma tailMappingBoundary_fibration (X Y : OmegaSpectrum.{u}) :
    Fibration (tailMappingBoundary X Y) := by
  let : Fibration (evaluation (tail X) (tail Y) 0) := evaluation_zero_fibration _ _
  let : Mono (X.sigma 0).right := X.sigma_mono 0
  let : Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma 0) (Y.level 1).space) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration _ _
  unfold tailMappingBoundary
  infer_instance

end SerrePositivity.KST.Spectra.OmegaSpectrum
