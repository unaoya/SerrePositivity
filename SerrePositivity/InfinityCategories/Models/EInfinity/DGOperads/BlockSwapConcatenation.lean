module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.BlockSwapRecursion

/-!
模型。文献の定義との比較は後で
# 連結したブロックの交換

概要：Berger–Moerdijk §1 の連結ブロックの交換を、二つのブロック交換に分解する。
方針：三つの入力区間ごとに位置を比較する。
規約：括弧付けの移送には自然数の結合則から得る標準全単射を使う。
使われ方：テンソル冪の braiding の hexagon と入力ブロックの交換を対応させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

/-- 概要：連結した左ブロックを二段で右へ移す全単射（Berger–Moerdijk §1）。
方針：左ブロックの後半、次に前半を右ブロックと交換する。
規約：三つのブロックの括弧付けを各段で移す。
使われ方：braiding の hexagon に対応する入力の全単射を表す。 -/
def operadBlockSwapConcat (l m n : ℕ) : Fin ((l + m) + n) ≃ Fin (n + (l + m)) :=
  (finCongr (Nat.add_assoc l m n)).trans
    ((_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin l)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap m n)).trans
      ((finCongr (Nat.add_assoc l n m).symm).trans
        ((_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap l n) (Equiv.refl (Fin m))).trans
          (finCongr (Nat.add_assoc n l m)))))

/-- 概要：二段の交換は連結ブロック全体の交換に一致する（Berger–Moerdijk §1）。
方針：左前半、左後半、右の各入力で値を比較する。
規約：いずれのブロックも空でよい。
使われ方：二つの小さい braiding から一般のブロック交換を計算する。 -/
lemma operadBlockSwap_concat (l m n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapConcat l m n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap (l + m) n := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x =>
    simp only [finSumFinEquiv_apply_left]
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
    cases x with
    | inl j =>
      simp only [finSumFinEquiv_apply_left]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
      have h₀ : finCongr (Nat.add_assoc l m n) ((j.castAdd m).castAdd n) =
          j.castAdd (m + n) := by apply Fin.ext; rfl
      have h₁ : finCongr (Nat.add_assoc l n m).symm (j.castAdd (n + m)) =
          (j.castAdd n).castAdd m := by apply Fin.ext; rfl
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapConcat, Equiv.trans_apply]
      rw [h₀, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, Equiv.refl_apply, h₁,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
      apply Fin.ext
      rfl
    | inr j =>
      simp only [finSumFinEquiv_apply_right]
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
      have h₀ : finCongr (Nat.add_assoc l m n) ((j.natAdd l).castAdd n) =
          (j.castAdd n).natAdd l := by apply Fin.ext; rfl
      have h₁ : finCongr (Nat.add_assoc l n m).symm ((j.natAdd n).natAdd l) =
          j.natAdd (l + n) := by apply Fin.ext; dsimp; omega
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapConcat, Equiv.trans_apply]
      rw [h₀, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left, h₁, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right]
      apply Fin.ext
      dsimp
      omega
  | inr j =>
    simp only [finSumFinEquiv_apply_right]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
    have h₀ : finCongr (Nat.add_assoc l m n) (j.natAdd (l + m)) =
        (j.natAdd m).natAdd l := by apply Fin.ext; dsimp; omega
    have h₁ : finCongr (Nat.add_assoc l n m).symm ((j.castAdd m).natAdd l) =
        (j.natAdd l).castAdd m := by apply Fin.ext; rfl
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapConcat, Equiv.trans_apply]
    rw [h₀, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right, h₁,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
    apply Fin.ext
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
