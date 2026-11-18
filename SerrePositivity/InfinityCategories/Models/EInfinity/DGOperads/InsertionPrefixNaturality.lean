module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionRotationCoherence

/-!
模型。文献の定義との比較は後で
# 代入の前方入力を越える係数の移動の自然性

概要：Berger–Moerdijk §1 の入力代入射で、後半の連結を係数と前方入力の交換へ通す。
方針：結合子と交換の自然性で後半の射を全体の後へ移す。
規約：係数 C と前方入力 W の交換だけを使い、後半 T の順序を保つ。
使われ方：三ブロックの入力表示で標準の代入射の連結と分離を相殺する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀] [SymmetricCategory C₀]

/-- 概要：係数を前方入力の後へ移す構造射は後半の射について自然である（Berger–Moerdijk §1）。
方針：右因子に関する結合子の自然性と交換則を順に使う。
規約：f は後半の入力の任意の射。
使われ方：後半の連結を逆の分離射まで通して相殺する。 -/
lemma insertionPrefix_naturality (C W : C₀) {T T' : C₀} (f : T ⟶ T') :
    (C ◁ (W ◁ f)) ≫ (α_ C W T').inv ≫ ((β_ C W).hom ▷ T') ≫ (α_ W C T').hom =
    (α_ C W T).inv ≫ ((β_ C W).hom ▷ T) ≫ (α_ W C T).hom ≫ (W ◁ (C ◁ f)) := by
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
