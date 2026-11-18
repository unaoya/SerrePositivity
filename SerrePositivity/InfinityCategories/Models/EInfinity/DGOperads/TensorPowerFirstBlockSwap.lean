module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerBlockSwap
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSwapNaturality

/-!
模型。文献の定義との比較は後で
# 三つの入力ブロックの先頭交換と連結

概要：Berger–Moerdijk §1 の三ブロックのうち先頭二つの交換をテンソル冪の作用と比較する。
方針：連結の結合則で先頭二つを括り、二ブロックの braiding の比較式を適用する。
規約：第三のブロックの順序は保つ。
使われ方：有限テンソル族の先頭の隣接交換と入力の連結を両立させる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.TensorPowers

/-- 概要：三つのブロックのうち先頭二つだけを交換する全単射（Berger–Moerdijk §1）。
方針：左括弧へ移し、先頭二つを交換して右括弧へ戻す。
規約：最後のブロックには恒等全単射を適用する。
使われ方：先頭の隣接交換が連結した入力に与える全単射を表す。 -/
def operadFirstBlockSwap (a b c : ℕ) : Fin (a + (b + c)) ≃ Fin (b + (a + c)) :=
  (finCongr (Nat.add_assoc a b c).symm).trans
    ((_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b) (Equiv.refl (Fin c))).trans
      (finCongr (Nat.add_assoc b a c)))

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：三ブロックの先頭二つの交換は連結後の全単射の作用と一致する（Berger–Moerdijk §1）。
方針：結合則、二ブロックの比較、連結の全単射に関する等変性を使う。
規約：始域の三因子は右括弧である。
使われ方：先頭の隣接交換の連結への作用を計算する。 -/
@[reassoc]
lemma appendIso_firstBlockSwap (X : C) (a b c : ℕ) :
    (α_ (power X a) (power X b) (power X c)).inv ≫
        ((β_ (power X a) (power X b)).hom ▷ power X c) ≫
        (α_ (power X b) (power X a) (power X c)).hom ≫
        (power X b ◁ (appendIso X a c).hom) ≫ (appendIso X b (a + c)).hom =
      (power X a ◁ (appendIso X b c).hom) ≫ (appendIso X a (b + c)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadFirstBlockSwap a b c) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadFirstBlockSwap, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_trans,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_finCongr]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_associativity_inv_assoc, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_equivariance_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_refl, tensorHom_id]
  rw [← comp_whiskerRight_assoc, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_blockSwap]
  simp only [comp_whiskerRight, Category.assoc]
  rw [appendIso_associativity]

/-- 概要：複体の三因子の交換は連結後のブロック交換を誘導する（Berger–Moerdijk §1）。
方針：三因子交換同型の定義を展開し、一般のモノイダル圏での比較式を使う。
規約：複体の対称性には Koszul 符号を含む。
使われ方：有限テンソル族の先頭二因子の交換の帰納法に用いる。 -/
@[reassoc]
lemma tensorTripleSwapIso_append {A : Type u} [CommRing A]
    (K : _root_.SerrePositivity.DifferentialGraded.Complex A) (a b c : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso (power K a) (power K b) (power K c)).hom ≫
        (power K b ◁ (appendIso K a c).hom) ≫ (appendIso K b (a + c)).hom =
      (power K a ◁ (appendIso K b c).hom) ≫ (appendIso K a (b + c)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap K (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadFirstBlockSwap a b c) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_firstBlockSwap K a b c

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
