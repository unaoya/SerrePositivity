module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.KanModels.GroupoidCompletionKanComparison
public import SerrePositivity.KST.LocalizingInvariants.LocalizationFactorization

/-! # 同じ評価の厳密 Kan 置換と、元の全辺局所化による比較の同値性判定 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.KanModels
open SerrePositivity.KST.Fibration
variable {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)

/-- Kan 標的の同じ置換単位は、実際の ∞ 圏同値。 -/
theorem strictKanCompletionUnit_isQCatEquivalence (Y : SSet.{u}) [KanComplex Y] :
    IsQCatEquivalence (X := Y) (Y := F2.continuousKanReplacement.obj Y)
      (F2.continuousKanReplacementUnit.app Y) := by
  apply isQCatEquivalence_of_anodyneQ_isIso
  exact SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne Y)

/-- 元の亜群化との比較の下で、厳密 Kan 写像は同じ全辺局所化の評価と自然同型。 -/
def strictKanEvaluationComparisonIso : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.KanModels.groupoidCompletionKanComparison X ≫ _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map f)
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation f ≫ F2.continuousKanReplacementUnit.app Y) := by
  apply localizationFactorizationIso _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_isLocalization X)
  have e₁ := FunctorIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluationIso (X := X) (F2.continuousKanReplacementUnit.app X))
    (_root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map f)
  have e₂ : FunctorIso
      (F2.continuousKanReplacementUnit.app X ≫ _root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map f)
      (f ≫ F2.continuousKanReplacementUnit.app Y) :=
    eqToIso (congrArg (fun m => HomotopyCategory.mk (functorVertex m))
      (F2.continuousKanReplacementUnit.naturality f).symm)
  have e₃ := FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluationIso f)
    (F2.continuousKanReplacementUnit.app Y)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.KanModels.groupoidCompletionKanComparison] using e₁ ≪≫ e₂ ≪≫ e₃.symm

/-- 厳密 Kan 置換での同値性は、既存の同じ亜群化後の評価の同値性と同値。 -/
theorem strictKanCompletion_map_equivalence_iff_evaluation :
    IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.F1.KanModels.strictKanCompletion.map f) ↔
      IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionEvaluation f) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.groupoidCompletionKanComparison_isQCatEquivalence X
  have ht := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanCompletionUnit_isQCatEquivalence Y
  have e := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanEvaluationComparisonIso f
  constructor
  · intro h
    exact ht.cancel_right ((hs.comp h).ofFunctorIso e)
  · intro h
    exact hs.cancel_left ((h.comp ht).ofFunctorIso e.symm)

end SerrePositivity.InfinityCategories.Derived.KanModels

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictKanCompletionUnit_isQCatEquivalence := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanCompletionUnit_isQCatEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictKanCompletion_map_equivalence_iff_evaluation := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanCompletion_map_equivalence_iff_evaluation

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanEvaluationComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictKanEvaluationComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanEvaluationComparisonIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictKanEvaluationComparisonIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanEvaluationComparisonIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictKanEvaluationComparisonIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanEvaluationComparisonIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.strictKanEvaluationComparisonIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.KanModels.strictKanEvaluationComparisonIso._proof_3
