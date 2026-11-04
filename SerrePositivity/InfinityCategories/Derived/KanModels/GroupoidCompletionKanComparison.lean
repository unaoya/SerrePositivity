module
public import SerrePositivity.KST.Fibration.GroupoidCompletionWeakUnit
public import SerrePositivity.InfinityCategories.F1.KanModels.StrictKanCompletion
public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionEvaluation
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy

/-! # 元の全辺局所化と厳密な Kan 亜群化模型との実比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の全辺局所化への単位そのものは anodyne 局所化同型。 -/
theorem groupoidCompletionUnit_anodyneQ_isIso (X : SSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (groupoidCompletionMap X)) :=
  weakHomotopyEquivalence_anodyneQ_isIso _ (groupoidCompletionUnit_isWeakHomotopyEquivalence X)

/-- 同じ連続 Kan 置換単位を、元の全辺局所化の実普遍性で下ろした比較射。 -/
def groupoidCompletionKanComparison (X : SSet.{u}) :
    groupoidCompletion X ⟶ (strictKanCompletion.obj X).obj :=
  groupoidCompletionEvaluation (F2.continuousKanReplacementUnit.app X)

/-- 元の普遍性による亜群化と、厳密 Kan 模型の比較は実際の Kan 同値。 -/
theorem groupoidCompletionKanComparison_isQCatEquivalence (X : SSet.{u}) :
    IsQCatEquivalence (groupoidCompletionKanComparison X) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hu : IsIso (Q.map (F2.continuousKanReplacementUnit.app X)) :=
    SSet.anodyneExtensions.Q_inverts _ (F2.continuousKanReplacementUnit_anodyne X)
  have hg := groupoidCompletionUnit_anodyneQ_isIso X
  have he : Q.map (groupoidCompletionMap X) ≫ Q.map (groupoidCompletionKanComparison X) =
      Q.map (F2.continuousKanReplacementUnit.app X) := by
    rw [← Q.map_comp]
    exact AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts
      (FunctorIso.simplicialHomotopy
        (groupoidCompletionEvaluationIso (F2.continuousKanReplacementUnit.app X)))
  have hc : IsIso (Q.map (groupoidCompletionMap X) ≫
      Q.map (groupoidCompletionKanComparison X)) := he.symm ▸ hu
  exact isQCatEquivalence_of_anodyneQ_isIso _ ((isIso_comp_left_iff _ _).mp hc)

end SerrePositivity.KST.Fibration
