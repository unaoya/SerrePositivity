module
public import SerrePositivity.KST.Fibration.GroupoidCompletionKanComparison
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
variable {X Y : SSet.{u}} [KanComplex Y] (f : X ⟶ Y)

/-- Kan 標的の同じ置換単位は、実際の ∞ 圏同値。 -/
theorem strictKanCompletionUnit_isQCatEquivalence (Y : SSet.{u}) [KanComplex Y] :
    IsQCatEquivalence (X := Y) (Y := F2.continuousKanReplacement.obj Y)
      (F2.continuousKanReplacementUnit.app Y) := by
  apply isQCatEquivalence_of_anodyneQ_isIso
  exact SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne Y)

/-- 元の亜群化との比較の下で、厳密 Kan 写像は同じ全辺局所化の評価と自然同型。 -/
def strictKanEvaluationComparisonIso : FunctorIso
    (groupoidCompletionKanComparison X ≫ strictKanCompletion.map f)
    (groupoidCompletionEvaluation f ≫ F2.continuousKanReplacementUnit.app Y) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
  have e₁ := FunctorIso.postcomp
    (groupoidCompletionEvaluationIso (X := X) (F2.continuousKanReplacementUnit.app X))
    (strictKanCompletion.map f)
  have e₂ : FunctorIso
      (F2.continuousKanReplacementUnit.app X ≫ strictKanCompletion.map f)
      (f ≫ F2.continuousKanReplacementUnit.app Y) :=
    eqToIso (congrArg (fun m => HomotopyCategory.mk (functorVertex m))
      (F2.continuousKanReplacementUnit.naturality f).symm)
  have e₃ := FunctorIso.postcomp (groupoidCompletionEvaluationIso f)
    (F2.continuousKanReplacementUnit.app Y)
  simpa only [Category.assoc, groupoidCompletionKanComparison] using e₁ ≪≫ e₂ ≪≫ e₃.symm

/-- 厳密 Kan 置換での同値性は、既存の同じ亜群化後の評価の同値性と同値。 -/
theorem strictKanCompletion_map_equivalence_iff_evaluation :
    IsQCatEquivalence (strictKanCompletion.map f) ↔
      IsQCatEquivalence (groupoidCompletionEvaluation f) := by
  have hs := groupoidCompletionKanComparison_isQCatEquivalence X
  have ht := strictKanCompletionUnit_isQCatEquivalence Y
  have e := strictKanEvaluationComparisonIso f
  constructor
  · intro h
    exact ht.cancel_right ((hs.comp h).ofFunctorIso e)
  · intro h
    exact hs.cancel_left ((h.comp ht).ofFunctorIso e.symm)

end SerrePositivity.KST.Fibration
