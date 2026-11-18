module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MoveFirstBlockTensor

/-!
模型。文献の定義との比較は後で
# 先頭一入力の移動とテンソル冪の連結

概要：Berger–Moerdijk §1 の代入結果の移動で、先頭の一入力に付く単位因子を除く。
方針：一次の標準連結を右単位子へ移し、交換と結合子の自然性を使う。
規約：先頭の対象 X を a 入力の後へ置き、末尾 b 入力を保つ。
使われ方：先頭で演算を適用してから回転する射を既存の代入射へ比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory
open _root_.SerrePositivity.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：先頭一入力の回転は一対象と前半のテンソル冪の交換で計算できる（Berger–Moerdijk §1）。
方針：先頭一ブロックの比較式へ右単位子を前置し、自然性で単位因子を除く。
規約：出力の長さは a+b+1。
使われ方：代入結果を指定位置へ動かすテンソル射の式を得る。 -/
lemma appendIso_moveFirstInput (X : C) (a b : ℕ) :
    (X ◁ (appendIso X a b).hom) ≫
      (permutationAction X (a + b + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b 1)).asIso.hom =
    (α_ X (power X a) (power X b)).inv ≫ ((β_ X (power X a)).hom ▷ power X b) ≫
      (α_ (power X a) X (power X b)).hom ≫ (appendIso X a (b + 1)).hom ≫
      eqToHom (congrArg (power X) (Nat.add_assoc a b 1).symm) := by
  apply (cancel_epi ((ρ_ X).hom ▷ (power X a ⊗ power X b))).1
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_moveFirstBlock X a b 1
  rw [appendIso_one_left, appendIso_one_left] at h
  simp only [whiskerLeft_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp] at h
  rw [appendIso_index_right_assoc X a (Nat.one_add b).symm] at h
  simp only [eqToHom_trans] at h
  rw [whisker_exchange_assoc] at h
  rw [← associator_naturality_middle_assoc] at h
  rw [← comp_whiskerRight_assoc, ← braiding_naturality_left, comp_whiskerRight_assoc] at h
  rw [← associator_inv_naturality_left_assoc] at h
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
