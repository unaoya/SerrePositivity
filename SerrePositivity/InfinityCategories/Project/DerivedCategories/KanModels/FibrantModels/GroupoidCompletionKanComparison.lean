module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.Fibration.WeakHomotopyAnodyneComparison
public import SerrePositivity.KST.Fibration.GroupoidCompletionWeakUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.StrictKanCompletion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 元の全辺局所化と厳密な Kan 亜群化模型との実比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels
open _root_.SerrePositivity.KST.Fibration

/-- 元の全辺局所化への単位そのものは anodyne 局所化同型。 -/
theorem groupoidCompletionUnit_anodyneQ_isIso (X : SSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap X)) :=
  weakHomotopyEquivalence_anodyneQ_isIso _ (groupoidCompletionUnit_isWeakHomotopyEquivalence X)

/-- 同じ連続 Kan 置換単位を、元の全辺局所化の実普遍性で下ろした比較射。 -/
def groupoidCompletionKanComparison (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.obj X).obj :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)

/-- 元の普遍性による亜群化と、厳密 Kan 模型の比較は実際の Kan 同値。 -/
theorem groupoidCompletionKanComparison_isQCatEquivalence (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.groupoidCompletionKanComparison X) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hu : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)) :=
    SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne X)
  have hg := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.groupoidCompletionUnit_anodyneQ_isIso X
  have he : Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap X) ≫ Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.groupoidCompletionKanComparison X) =
      Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X) := by
    rw [← Q.map_comp]
    exact AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEvaluationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app X)))
  have hc : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap X) ≫
      Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.groupoidCompletionKanComparison X)) := he.symm ▸ hu
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isQCatEquivalence_of_anodyneQ_isIso _ ((isIso_comp_left_iff _ _).mp hc)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
