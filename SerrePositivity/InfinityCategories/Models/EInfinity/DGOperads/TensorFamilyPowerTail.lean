module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacentTail

/-!
模型。文献の定義との比較は後で
# 尾の置換後のテンソル冪の連結

概要：Berger–Moerdijk §1 の尾の入力置換に対して有限テンソル族の連結を展開する。
方針：先頭を保った有限族を構成し、添字の等式による移送と連結の先頭の再帰を使う。
規約：先頭のブロックの長さと尾の総和を右括弧で連結する。
使われ方：隣接交換と連結の両立を尾へ帰納する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] _root_.SerrePositivity.TensorPowers.power _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso

/-- 概要：連結の先頭の一ブロックを展開する（Berger–Moerdijk §1）。
方針：連結同型の再帰を一回評価し、総和の移送を消す。
規約：尾は空でもよい。
使われ方：尾の置換後の連結を先頭の whisker として記述する。 -/
@[reassoc]
lemma tensorPowerFamilyIso_head (K : Complex A) (n : ℕ) (s : Fin (n + 1) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) s).hom ≫
        eqToHom (congrArg (power K) (Fin.sum_univ_succ s)) =
      (power K (s 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ)).hom) ≫
        (appendIso K (s 0) (∑ i : Fin n, s i.succ)).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- 概要：先頭を固定して尾に置換を適用した具体的な長さの族（Berger–Moerdijk §1）。
方針：先頭と尾を cases で分ける。
規約：尾の置換は任意の対称群の元でよい。
使われ方：尾の置換の対象と総和の比較を独立して検証する。 -/
def tensorPowerTailFamily (n : ℕ) (s : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    Fin (n + 1) → ℕ := fun i => Fin.cases (s 0) (fun j => s (σ j).succ) i

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily

/-- 概要：具体的な尾の置換族はずらした置換による引き戻しに等しい（Berger–Moerdijk §1）。
方針：先頭と尾で既存のずらした置換を評価する。
規約：先頭の位置は 0。
使われ方：連結の添字族の比較補題に適用する。 -/
lemma tensorPowerTailFamily_eq (n : ℕ) (s : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily n s σ = (fun i => s (shiftPerm σ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg s (shiftPerm_zero σ).symm
  · exact congrArg s (shiftPerm_succ σ j).symm

/-- 概要：尾の置換族の対象を先頭と尾へ分ける（Berger–Moerdijk §1）。
方針：有限テンソルの先頭の再帰を評価する。
規約：尾の長さは n。
使われ方：連結の始域を先頭の whisker の始域へ移す。 -/
lemma tensorPowerTailFamily_obj (K : Complex A) (n : ℕ) (s : Fin (n + 1) → ℕ)
    (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun i => power K (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily n s σ i)) =
      power K (s 0) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => power K (s (σ i).succ)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily, Fin.cases_zero, Fin.cases_succ]

/-- 概要：尾の置換族の総和を先頭と尾へ分ける（Berger–Moerdijk §1）。
方針：有限和の先頭を分離する。
規約：尾の入力の順序を置換後のものとする。
使われ方：連結の終域を先頭の長さと尾の総和の和へ移す。 -/
lemma tensorPowerTailFamily_sum (n : ℕ) (s : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    (∑ i, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily n s σ i) = s 0 + ∑ i : Fin n, s (σ i).succ := by
  rw [Fin.sum_univ_succ]
  rfl

/-- 概要：ずらした置換後の総和を先頭と尾へ分ける（Berger–Moerdijk §1）。
方針：先頭の分離の後でずらした置換の値を計算する。
規約：先頭は固定される。
使われ方：尾の隣接交換の終域の移送に使う。 -/
lemma tensorFamily_sum_shift (n : ℕ) (s : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin n)) :
    (∑ i, s (shiftPerm σ i)) = s 0 + ∑ i : Fin n, s (σ i).succ := by
  rw [Fin.sum_univ_succ]
  simp only [shiftPerm_zero, shiftPerm_succ]

/-- 概要：尾の隣接交換後の総和を先頭と尾へ分ける（Berger–Moerdijk §1）。
方針：尾の隣接交換をずらした置換として表す。
規約：元の入力の長さは n+2。
使われ方：全ての位置のブロック交換を再帰的に定義する。 -/
lemma tensorFamily_sum_adjacentSucc (n : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n) :
    (∑ j, s (adjacentTransposition i.succ j)) =
      s 0 + ∑ j : Fin (n + 1), s (adjacentTransposition i j).succ := by
  rw [← shiftPerm_adjacent n i]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_shift (n + 1) s (adjacentTransposition i)

/-- 概要：具体的な尾の置換族の連結を先頭で展開する（Berger–Moerdijk §1）。
方針：連結の先頭の再帰の前後に対象と総和の移送を合成する。
規約：終域は先頭と尾の長さの和である。
使われ方：隣接交換後の連結を帰納法の尾の連結へ移す。 -/
lemma tensorPowerTailFamily_expand (K : Complex A) (n : ℕ) (s : Fin (n + 1) → ℕ)
    (σ : Equiv.Perm (Fin n)) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily_obj K n s σ).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily n s σ)).hom ≫
        eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily_sum n s σ)) =
      (power K (s 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s (σ i).succ)).hom) ≫
        (appendIso K (s 0) (∑ i : Fin n, s (σ i).succ)).hom := by
  have h := congrArg (fun f => eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily_obj K n s σ).symm ≫ f)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_head K n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily n s σ))
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily, Fin.cases_zero, Fin.cases_succ] at h
  conv at h =>
    rhs
    erw [eqToHom_refl, Category.id_comp]
  exact h

/-- 概要：尾の隣接交換後の連結を先頭の whisker で表す（Berger–Moerdijk §1）。
方針：具体的な尾の置換族と隣接互換を比較してから連結の展開を使う。
規約：先頭のブロックは保持する。
使われ方：有限テンソル族の隣接交換と連結の両立の帰納段階に使う。 -/
lemma tensorPowerFamilyIso_adjacentSucc_transport (K : Complex A)
    (n : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n (fun j => power K (s j)) i).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 2) (fun j => s (adjacentTransposition i.succ j))).hom ≫
        eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_adjacentSucc n s i)) =
      (power K (s 0) ◁
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) (fun j => s (adjacentTransposition i j).succ)).hom) ≫
        (appendIso K (s 0) (∑ j : Fin (n + 1), s (adjacentTransposition i j).succ)).hom := by
  have hi := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily_eq (n + 1) s (adjacentTransposition i)).trans
    (congrArg (fun σ : Equiv.Perm (Fin (n + 2)) => fun j => s (σ j)) (shiftPerm_adjacent n i))
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_compare K (n + 2) hi
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily_obj K (n + 1) s (adjacentTransposition i))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n (fun j => power K (s j)) i)
    (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily_sum (n + 1) s (adjacentTransposition i)))
    (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_adjacentSucc n s i))).trans
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerTailFamily_expand K (n + 1) s (adjacentTransposition i))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
