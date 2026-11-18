module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerAdjacent

/-!
模型。文献の定義との比較は後で
# テンソル族の隣接交換の出力の値

概要：Berger–Moerdijk §1 の外側等変性で現れる二つの出力の全単射を比較する。
方針：先頭からの再帰でも中央の二ブロックだけを交換する四区間の式を証明する。
規約：ブロックの長さ零を許し、各ブロック内の位置を保つ。
使われ方：反復合成の等変性をテンソル冪の連結の等変性へ接続する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

private lemma blockEquiv_zero_left_val {a b : ℕ} (e : Fin a ≃ Fin b)
    (x : Fin (0 + a)) :
    (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin 0)) e x).val =
      (e (finCongr (Nat.zero_add a) x)).val := by
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x => exact Fin.elim0 x
  | inr x =>
    simp only [finSumFinEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, Fin.val_natAdd,
      Nat.zero_add]
    have h : finCongr (Nat.zero_add a) (x.natAdd 0) = x := by
      apply Fin.ext
      dsimp
      omega
    rw [h]

/-- 概要：先頭二ブロックの交換の値を区間ごとに計算する（Berger–Moerdijk §1）。
方針：前方の長さが零の中央交換の式を適用する。
規約：三番目のブロック c 個は固定する。
使われ方：テンソル族の隣接交換の値の帰納法の先頭の場合に用いる。 -/
lemma operadFirstBlockSwap_val (a b c : ℕ) (x : Fin (a + (b + c))) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadFirstBlockSwap a b c x).val =
      if x.val < a then x.val + b else
      if x.val < a + b then x.val - a else x.val := by
  let y : Fin (((0 + c) + a) + b) := finCongr (by omega) x
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap_val 0 c a b y
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadContextBlockSwap, Equiv.trans_apply, finCongr_apply_coe,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_zero_left_val, Nat.zero_add, Nat.not_lt_zero, ite_false] at h
  exact h

/-- 概要：先頭を固定して尾で交換すると、前方の総長には先頭の長さが加わる（Berger–Moerdijk §1）。
方針：前方の和を先頭と尾に分解する。
規約：入力は n+2 個で、交換位置は i.succ。
使われ方：先頭からの再帰で四区間の境界を移す。 -/
lemma operadAdjacentPrefixLength_succ (n : ℕ) (s : Fin (n + 2) → ℕ) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength (n + 1) s i.succ =
      s 0 + _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength n (fun j => s j.succ) i := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength
  change (∑ j : Fin (i.val + 1), s ⟨j.val, by omega⟩) = _
  rw [Fin.sum_univ_succ]
  rfl

/-- 概要：先頭二ブロックの交換の連結後の値を四区間で表す（Berger–Moerdijk §1）。
方針：三つのブロックへの arity の移送が値を保つことを使う。
規約：残りの入力の総長は固定される。
使われ方：任意のテンソル族の隣接交換の値の帰納法の基底となる。 -/
lemma tensorFamilyFirstBlockEquiv_val (n : ℕ) (s : Fin (n + 2) → ℕ)
    (x : Fin (∑ j, s j)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstBlockEquiv n s x).val =
      if x.val < s 0 then x.val + s 1 else
      if x.val < s 0 + s 1 then x.val - s 0 else x.val := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadFirstBlockSwap_val (s 0) (s 1) (∑ j : Fin n, s j.succ.succ)
    (finCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_two n s) x)

/-- 概要：テンソル族の隣接ブロック交換は中央の二ブロックだけを交換する（Berger–Moerdijk §1）。
方針：先頭の交換の式を使い、尾の場合は先頭を除いた値へ帰納仮定を適用する。
規約：交換位置より前の総長は operadAdjacentPrefixLength で表す。
使われ方：反復合成の出力の全単射との同定に用いる。 -/
lemma tensorFamilyAdjacentBlockEquiv_val (n : ℕ) (s : Fin (n + 1) → ℕ)
    (i : Fin n) (x : Fin (∑ j, s j)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentBlockEquiv n s i x).val =
      let p := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength n s i
      let a := s i.castSucc
      let b := s i.succ
      if x.val < p then x.val else
      if x.val < p + a then x.val + b else
      if x.val < p + a + b then x.val - a else x.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentBlockEquiv_zero]
      have hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength (n + 1) s 0 = 0 := by
        change (∑ j : Fin 0, s ⟨j.val, by omega⟩) = 0
        exact Fin.sum_univ_zero _
      simp only [hp, Nat.not_lt_zero, ite_false, Nat.zero_add]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstBlockEquiv_val n s x
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentBlockEquiv_succ]
      let y := finCongr (Fin.sum_univ_succ s) x
      obtain ⟨z, hz⟩ := finSumFinEquiv.surjective y
      cases z with
      | inl z =>
        have hx : finCongr (Fin.sum_univ_succ s) x =
            z.castAdd (∑ j : Fin (n + 1), s j.succ) := hz.symm
        have hv := congrArg Fin.val hx
        simp only [Equiv.trans_apply, hx, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, Equiv.refl_apply,
          finCongr_apply_coe, Fin.val_castAdd]
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength_succ]
        simp only [finCongr_apply_coe, Fin.val_castAdd] at hv
        split_ifs <;> omega
      | inr z =>
        have hx : finCongr (Fin.sum_univ_succ s) x = z.natAdd (s 0) := hz.symm
        have hv := congrArg Fin.val hx
        simp only [Equiv.trans_apply, hx, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, finCongr_apply_coe,
          Fin.val_natAdd]
        have h := ih (fun j => s j.succ) j z
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength_succ]
        simp only [finCongr_apply_coe, Fin.val_natAdd] at hv
        rw [h]
        dsimp only
        change x.val = s 0 + z.val at hv
        have ha : s j.castSucc.succ = s j.succ.castSucc := rfl
        rw [ha]
        split_ifs <;> omega

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
