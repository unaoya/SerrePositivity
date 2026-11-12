module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionColumnMarked
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstColumn

/-!
# 元の最初の非指定列と語の圧縮・恒等列の挿入

概要：圧縮後の最小非指定列は、元の最小非指定列の像に厳密に一致する。
方針：元の各 fiber の空文字列の判定と最小性を使う。
規約：空 fiber を含む元の任意の語の射を使う。
使われ方：prefix と残りの全語への整合。

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
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X Y)

lemma column_wordAction_nonempty (i : Fin a.length) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (f.orderHom i) ≠ [] := by
  intro h
  exact hi ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.column_wordAction_eq_nil_iff W f S (f.orderHom i)).1 h i rfl)

lemma nonemptyColumns_wordAction (h : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ []) :
    ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j ≠ [] := by
  obtain ⟨i, hi⟩ := h
  exact ⟨f.orderHom i, column_wordAction_nonempty W f S i hi⟩

lemma firstColumn_wordAction (hS : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ [])
    (hT : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) hT = f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W S hS) := by
  apply le_antisymm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_le W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) hT _
      (column_wordAction_nonempty W f S _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W S hS))
  · classical
    let j := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) hT
    have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) hT
    have hex : ∃ i, f.orderHom i = j ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W S i ≠ [] := by
      by_contra hn
      apply hj
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.column_wordAction_eq_nil_iff W f S j).2
      intro i hi
      by_contra he
      exact hn ⟨i, hi, he⟩
    obtain ⟨i, hi, he⟩ := hex
    exact (f.orderHom.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_le W S hS i he)).trans_eq hi

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
