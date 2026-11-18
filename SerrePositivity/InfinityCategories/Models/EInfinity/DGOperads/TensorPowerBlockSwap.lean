module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.BlockSwapConcatenation
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic

/-!
模型。文献の定義との比較は後で
# テンソル冪の連結と入力ブロックの交換

概要：Berger–Moerdijk §1 の入力ブロック交換が、テンソル冪の braiding を誘導することを証明する。
方針：空のブロック、一入力の巡回移動、交換の再帰を使う。
規約：連結の長さの等式は標準全単射の関手で移送する。
使われ方：Schur 演算の外側等変性で係数のブロック交換と入力の交換を比較する。
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

/-- 概要：空の左ブロックの braiding と全単射の作用は一致する（Berger–Moerdijk §1）。
方針：左単位子と右単位子による braiding の式を使う。
規約：左ブロックの長さは 0。
使われ方：入力ブロック交換の帰納法の基底を与える。 -/
lemma appendIso_blockSwap_zero (X : C) (b : ℕ) :
    (β_ (power X 0) (power X b)).hom ≫ (appendIso X b 0).hom =
      (appendIso X 0 b).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap 0 b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_finCongr,
    appendIso_zero_left, appendIso_zero_right]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact braiding_rightUnitor _

/-- 概要：一入力のブロック交換はテンソル冪の braiding を誘導する（Berger–Moerdijk §1）。
方針：先頭を末尾へ送る巡回置換と右単位子の比較を使う。
規約：長さ 1+b と b+1 の移送を明示する。
使われ方：一般のブロック交換を小さい交換へ分解する帰納法に使う。 -/
lemma appendIso_blockSwap_one (X : C) (b : ℕ) :
    (β_ (power X 1) (power X b)).hom ≫ (appendIso X b 1).hom =
      (appendIso X 1 b).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap 1 b) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_one, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_trans, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_finCongr,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_perm, permutationAction_firstToLast, appendIso_one_left]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]
  exact oneCrossing_comparison X b

omit [SymmetricCategory C] in
/-- 概要：三つのテンソル冪の右括弧の連結を左括弧へ移す（Berger–Moerdijk §1）。
方針：連結の結合則の前後に逆の結合子と長さの移送を合成する。
規約：終域は左括弧の和次数とする。
使われ方：二段のブロック交換の中間の連結を整理する。 -/
@[reassoc]
lemma appendIso_associativity_inv (X : C) (l m n : ℕ) :
    (power X l ◁ (appendIso X m n).hom) ≫ (appendIso X l (m + n)).hom ≫
        eqToHom (congrArg (power X) (Nat.add_assoc l m n).symm) =
      (α_ (power X l) (power X m) (power X n)).inv ≫
        ((appendIso X l m).hom ▷ power X n) ≫ (appendIso X (l + m) n).hom := by
  have h := congrArg (fun f =>
    (α_ (power X l) (power X m) (power X n)).inv ≫ f ≫
      eqToHom (congrArg (power X) (Nat.add_assoc l m n).symm))
    (appendIso_associativity X l m n).symm
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] using h

/-- 概要：二つのブロック交換の比較から連結ブロックの比較を得る（Berger–Moerdijk §1）。
方針：全単射の分解を連結の等変性で展開し、braiding の hexagon と比較する。
規約：仮定は左右の小さいブロック交換の比較式である。
使われ方：空および一入力の比較から任意の長さの比較を帰納的に導く。 -/
lemma appendIso_blockSwap_add (X : C) (l m n : ℕ)
    (hl : (β_ (power X l) (power X n)).hom ≫ (appendIso X n l).hom =
      (appendIso X l n).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap l n))
    (hm : (β_ (power X m) (power X n)).hom ≫ (appendIso X n m).hom =
      (appendIso X m n).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n)) :
    (β_ (power X (l + m)) (power X n)).hom ≫ (appendIso X n (l + m)).hom =
      (appendIso X (l + m) n).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap (l + m) n) := by
  apply (cancel_epi ((appendIso X l m).hom ▷ power X n)).1
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_concat]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapConcat, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_trans,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_finCongr]
  rw [reassoc_of% (appendIso_associativity X l m n)]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_equivariance_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_refl, id_tensorHom]
  rw [← whiskerLeft_comp_assoc, ← hm]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_associativity_inv_assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_equivariance_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap_refl, tensorHom_id]
  rw [← comp_whiskerRight_assoc, ← hl]
  simp only [comp_whiskerRight, Category.assoc]
  rw [appendIso_associativity]
  rw [braiding_naturality_left_assoc, braiding_tensor_left_hom]
  simp only [Category.assoc]

/-- 概要：任意の二つの入力ブロックの交換はテンソル冪の braiding を誘導する（Berger–Moerdijk §1）。
方針：左ブロックの長さで帰納し、一入力の比較と連結の hexagon を使う。
規約：入力のテンソル冪は右括弧とし、長さの式の違いは有限全単射で移す。
使われ方：外側の入力交換で生じる全入力のブロック置換を計算する。 -/
@[reassoc]
lemma appendIso_blockSwap (X : C) (a b : ℕ) :
    (β_ (power X a) (power X b)).hom ≫ (appendIso X b a).hom =
      (appendIso X a b).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap X (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b) := by
  induction a with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_blockSwap_zero X b
  | succ a ih =>
    have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_blockSwap_add X 1 a b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.appendIso_blockSwap_one X b) ih
    rw [show 1 + a = a + 1 by omega] at h
    exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
