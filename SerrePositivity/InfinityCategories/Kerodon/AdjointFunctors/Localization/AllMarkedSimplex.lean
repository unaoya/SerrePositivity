module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyReflection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagReflection

/-!
# 元の全行の全列の指定性と全作用への反映

概要：元の単体の全横列が指定である条件を、基準行の非指定列の不存在で判定する。
方針：元の全行の列の文字列の一致と全作用の非空性の保存・反映を使う。
規約：全行・全列・空語を含む。
使われ方：指定部分圏の実際の hammock と空文字列部分の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}

abbrev Holds (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) := ∀ d j, W.paths ((τ.obj d).arrow j)

lemma holds_iff (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ ↔ ¬ ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [] := by
  classical
  constructor
  · intro h ⟨j, hj⟩
    exact hj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W _ (h 0 j))
  · intro h d j
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_eq_nil_iff W _).1
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj d) j = []
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column_row W τ d j]
    by_contra hj
    exact h ⟨j, hj⟩

lemma holds_simplex_iff (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (θ : n ⟶ m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.holds_iff, holds_iff, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_simplex_iff]

lemma holds_word_iff {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.holds_iff, holds_iff]
  exact not_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_wordAction_iff W f (τ.obj 0))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
