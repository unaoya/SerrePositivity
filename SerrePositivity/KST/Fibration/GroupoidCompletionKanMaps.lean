module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.GroupoidCompletionKanComparison

/-! # 元の亜群化後の実写像と厳密 Kan 置換後の実写像の可逆性の比較 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の全辺局所化の自然な因子化同型によって、亜群化後と元の射の局所化可逆性は同値。 -/
theorem groupoidCompletionMapOf_anodyneQ_isIso_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.groupoidCompletionUnit_anodyneQ_isIso X
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.groupoidCompletionUnit_anodyneQ_isIso Y
  have he : Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap X) ≫ Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f) =
      Q.map f ≫ Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap Y) := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOfIso f))
  calc
    _ ↔ IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap X) ≫ Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f)) :=
      (isIso_comp_left_iff _ _).symm
    _ ↔ IsIso (Q.map f ≫ Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap Y)) := by rw [he]
    _ ↔ _ := isIso_comp_right_iff _ _

/-- 指定した同じ射の亜群化が同値なら、厳密 Kan 模型の同じ像も実際の同値。 -/
theorem strictKanCompletion_map_isQCatEquivalence_of_groupoidCompletion
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion.map f) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.strictKanCompletion_map_isQCatEquivalence f
    ((groupoidCompletionMapOf_anodyneQ_isIso_iff f).mp hf.anodyneQ_isIso)

end SerrePositivity.KST.Fibration
