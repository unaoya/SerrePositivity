module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorWord

/-!
# 元の射列の最初の非指定生成矢での切断

概要：非指定文字を含む元の射列を、指定接頭列・最初の非指定生成矢・残りへ分ける。
方針：元の射列の cons に沿って帰納し、指定接頭列を厳密に回収する。
規約：元の生成矢の始域・終域・射と元の連結の等式を保持する。
使われ方：不変な非指定文字列に沿う hammock の各行の切断。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

lemma exists_first_unmarked {X Y : C} (p : Quiver.Path X Y) (hp : ¬ W.paths p) :
    ∃ (A B : C) (e : A ⟶ B) (left : Quiver.Path X A) (right : Quiver.Path B Y),
      W.paths left ∧ ¬ W e ∧ p = left.comp (e.toPath.comp right) := by
  classical
  induction p with
  | nil => exact (hp trivial).elim
  | cons p f ih =>
    by_cases hleft : W.paths p
    · refine ⟨_, _, f, p, .nil, hleft, ?_, rfl⟩
      intro hf
      exact hp ⟨hleft, hf⟩
    · obtain ⟨A, B, e, left, right, hl, he, rfl⟩ := ih hleft
      exact ⟨A, B, e, left, right.cons f, hl, he, rfl⟩

lemma exists_first_of_erase_ne_nil {X Y : C} (p : Quiver.Path X Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W p ≠ []) :
    ∃ (A B : C) (e : A ⟶ B) (left : Quiver.Path X A) (right : Quiver.Path B Y),
      W.paths left ∧ ¬ W e ∧ p = left.comp (e.toPath.comp right) :=
  exists_first_unmarked W p (fun h => hp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W p h))

lemma erase_first_split {X A B Y : C} (left : Quiver.Path X A) (e : A ⟶ B)
    (right : Quiver.Path B Y) (hl : W.paths left) (he : ¬ W e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W (left.comp (e.toPath.comp right)) = ⟨A, B, e⟩ :: _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase W right := by
  classical
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W left hl, Quiver.Hom.toPath, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase, he]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
