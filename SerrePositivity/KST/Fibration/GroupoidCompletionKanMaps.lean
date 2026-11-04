module
public import SerrePositivity.InfinityCategories.Derived.KanModels.GroupoidCompletionKanComparison

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
    IsIso (AnodyneHomotopy.anodyneQ.map (groupoidCompletionMapOf f)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := groupoidCompletionUnit_anodyneQ_isIso X
  have := groupoidCompletionUnit_anodyneQ_isIso Y
  have he : Q.map (groupoidCompletionMap X) ≫ Q.map (groupoidCompletionMapOf f) =
      Q.map f ≫ Q.map (groupoidCompletionMap Y) := by
    rw [← Q.map_comp, ← Q.map_comp]
    exact AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts
      (FunctorIso.simplicialHomotopy (groupoidCompletionMapOfIso f))
  calc
    _ ↔ IsIso (Q.map (groupoidCompletionMap X) ≫ Q.map (groupoidCompletionMapOf f)) :=
      (isIso_comp_left_iff _ _).symm
    _ ↔ IsIso (Q.map f ≫ Q.map (groupoidCompletionMap Y)) := by rw [he]
    _ ↔ _ := isIso_comp_right_iff _ _

/-- 指定した同じ射の亜群化が同値なら、厳密 Kan 模型の同じ像も実際の同値。 -/
theorem strictKanCompletion_map_isQCatEquivalence_of_groupoidCompletion
    {X Y : SSet.{u}} (f : X ⟶ Y) (hf : IsQCatEquivalence (groupoidCompletionMapOf f)) :
    IsQCatEquivalence (strictKanCompletion.map f) :=
  strictKanCompletion_map_isQCatEquivalence f
    ((groupoidCompletionMapOf_anodyneQ_isIso_iff f).mp hf.anodyneQ_isIso)

end SerrePositivity.KST.Fibration
