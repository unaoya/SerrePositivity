module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedNonemptyWordDiagram

/-!
# 元の全語と全単体作用素による非空列の反映

概要：非空の非指定列を持つ条件は元の全作用によって保存され反映される。
方針：全行での列の一致と元の各 fiber の空文字列の判定を使う。
規約：空 fiber と空語を含む元の任意の語の射を扱う。
使われ方：非空部分の余極限の元の hammock 内での同定。

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
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C}

lemma nonemptyColumns_wordAction_iff (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y) :
    (∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j ≠ []) ↔ ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ [] := by
  constructor
  · rintro ⟨j, hj⟩
    by_contra hn
    apply hj
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.column_wordAction_eq_nil_iff W f S j).2
    intro i _
    by_contra hi
    exact hn ⟨i, hi⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.nonemptyColumns_wordAction W f S

lemma nonemptyColumns_simplex_iff {n m : SimplexCategoryᵒᵖ}
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n) (θ : n ⟶ m) :
    (∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).map θ τ).obj 0) j ≠ []) ↔
      ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) j ≠ [] := by
  change (∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj (θ.unop.toOrderHom 0)) j ≠ []) ↔ _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column_row W τ]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
