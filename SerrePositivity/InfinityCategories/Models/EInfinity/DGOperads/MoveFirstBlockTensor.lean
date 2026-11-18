module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MoveFirstBlock

/-!
模型。文献の定義との比較は後で
# 先頭ブロックの移動のテンソル冪への作用

概要：Berger–Moerdijk §1 の挿入位置の移動を、テンソル冪の連結とブロック交換で計算する。
方針：arity の表示を移す全単射を三ブロック交換の前後へ合成する。
規約：入力ブロックの長さは p,a,b、全体の長さを a+b+p と表す。
使われ方：先頭の入力作用を指定位置への入力代入射へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：先頭ブロックを移す入力置換は三因子の交換と連結で計算できる（Berger–Moerdijk §1）。
方針：置換を arity の移送と三ブロック交換へ分解し、既存の交換と連結の比較式を使う。
規約：最後の b 入力の順序を保存する。
使われ方：代入前後の先頭ブロックの回転をテンソルの構造射へ変える。 -/
lemma appendIso_moveFirstBlock (X : C) (a b p : ℕ) :
    (power X p ◁ (appendIso X a b).hom) ≫ (appendIso X p (a + b)).hom ≫
      eqToHom (congrArg (power X) (by omega : p + (a + b) = a + b + p)) ≫
      (permutationAction X (a + b + p) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock a b p)).asIso.hom =
    (α_ (power X p) (power X a) (power X b)).inv ≫
      ((β_ (power X p) (power X a)).hom ▷ power X b) ≫
      (α_ (power X a) (power X p) (power X b)).hom ≫
      (power X a ◁ (appendIso X p b).hom) ≫ (appendIso X a (p + b)).hom ≫
      eqToHom (congrArg (power X) (by omega : a + (p + b) = a + b + p)) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_perm]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadMoveFirstBlock, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_trans,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_finCongr, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_firstBlockSwap X p a b)]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
