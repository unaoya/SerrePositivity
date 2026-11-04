module

public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletionMaps

/-!
概要：Kan 値評価は亜群化に降下し、trivial Kan fibration による模型変更と整合する。
方針：実因子化の同型を前合成で比較し、亜群化後の射影同値で同値性を反映する。
規約：評価自体の同値性は仮定なしでは主張しない。
使われ方：分数評価の同値性を三角補完を記憶した模型で証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X A Y : SSet.{u}} [KanComplex Y]

def groupoidCompletionEvaluation (f : X ⟶ Y) : groupoidCompletion X ⟶ Y :=
  localizationDescend _ _ (groupoidCompletion_isLocalization X) f (invertsAllEdges_toKan f)

def groupoidCompletionEvaluationIso (f : X ⟶ Y) :
    FunctorIso (groupoidCompletionMap X ≫ groupoidCompletionEvaluation f) f :=
  localizationDescendIso _ _ (groupoidCompletion_isLocalization X) f (invertsAllEdges_toKan f)

def groupoidCompletionEvaluation_precompIso (p : A ⟶ X) (f : X ⟶ Y) :
    FunctorIso (groupoidCompletionMapOf p ≫ groupoidCompletionEvaluation f)
      (groupoidCompletionEvaluation (p ≫ f)) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization A)
  have h := FunctorIso.postcomp (groupoidCompletionMapOfIso p)
      (groupoidCompletionEvaluation f) ≪≫
    FunctorIso.precomp (groupoidCompletionEvaluationIso f) p ≪≫
    (groupoidCompletionEvaluationIso (p ≫ f)).symm
  simpa only [Category.assoc] using h

def groupoidCompletionEvaluation_functorIso {f g : X ⟶ Y} (e : FunctorIso f g) :
    FunctorIso (groupoidCompletionEvaluation f) (groupoidCompletionEvaluation g) := by
  apply localizationFactorizationIso _ _ (groupoidCompletion_isLocalization X)
  exact groupoidCompletionEvaluationIso f ≪≫ e ≪≫ (groupoidCompletionEvaluationIso g).symm

lemma groupoidCompletionEvaluation_trivialKanFibration_iff (p : A ⟶ X)
    [TrivialKanFibration p] (f : X ⟶ Y) :
    IsSimplicialHomotopyEquivalence (groupoidCompletionEvaluation (p ≫ f)) ↔
      IsSimplicialHomotopyEquivalence (groupoidCompletionEvaluation f) := by
  have hp := (groupoidCompletionEquivalenceOfTrivialKanFibration p).isQCatEquivalence
  change IsQCatEquivalence (groupoidCompletionMapOf p) at hp
  constructor
  · intro h
    have hcomp := h.isQCatEquivalence.ofFunctorIso
      (groupoidCompletionEvaluation_precompIso p f).symm
    exact (hp.cancel_left hcomp).isSimplicialHomotopyEquivalence
  · intro h
    exact ((hp.comp h.isQCatEquivalence).ofFunctorIso
      (groupoidCompletionEvaluation_precompIso p f)).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
