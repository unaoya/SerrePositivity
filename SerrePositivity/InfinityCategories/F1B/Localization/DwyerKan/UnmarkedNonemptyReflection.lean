module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedNonemptyWordDiagram

/-!
# 元の全語と全単体作用素による非空列の反映

概要：非空の非指定列を持つ条件は元の全作用によって保存され反映される。
方針：全行での列の一致と元の各 fiber の空文字列の判定を使う。
規約：空 fiber と空語を含む元の任意の語の射を扱う。
使われ方：非空部分の余極限の元の hammock 内での同定。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C}

lemma nonemptyColumns_wordAction_iff (f : a ⟶ b) (S : Zigzag W.paths a X Y) :
    (∃ j, column W (WordAction.obj f S) j ≠ []) ↔ ∃ i, column W S i ≠ [] := by
  constructor
  · rintro ⟨j, hj⟩
    by_contra hn
    apply hj
    apply (column_wordAction_eq_nil_iff W f S j).2
    intro i _
    by_contra hi
    exact hn ⟨i, hi⟩
  · exact nonemptyColumns_wordAction W f S

lemma nonemptyColumns_simplex_iff {n m : SimplexCategoryᵒᵖ}
    (τ : (graph W.paths a X Y).obj n) (θ : n ⟶ m) :
    (∃ j, column W (((graph W.paths a X Y).map θ τ).obj 0) j ≠ []) ↔
      ∃ j, column W (τ.obj 0) j ≠ [] := by
  change (∃ j, column W (τ.obj (θ.unop.toOrderHom 0)) j ≠ []) ↔ _
  simp only [column_row W τ]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
