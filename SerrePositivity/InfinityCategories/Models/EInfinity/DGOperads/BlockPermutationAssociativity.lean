module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SlotPermutations

/-!
模型。文献の定義との比較は後で
# ブロック置換の結合性と arity の移送

概要：Berger–Moerdijk §1 の全入力への合成で、内側の入力ブロックの括弧付けを比較する。
方針：三つのブロックの各入力で、二つの括弧付けの置換を計算する。
規約：括弧付けの変更は標準有限集合の長さの等式による同値を用いる。
使われ方：最後の入力から行う代入と、先頭から連結する入力の置換を接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

private lemma finCongr_permCongr_val {r s : ℕ} (h : r = s) (σ : Equiv.Perm (Fin r))
    (x : Fin s) :
    (((finCongr h).permCongr σ) x).val = (σ ⟨x.val, by omega⟩).val := by
  subst s
  rfl

/-- 概要：arity の等式による置換の移送は等式の合成を保つ（Berger–Moerdijk §1）。
方針：二つの等式で長さを同一視し、移送の定義を簡約する。
規約：Fin 上の置換を長さの等式に沿って共役する。
使われ方：全入力の arity の括弧付けに由来する複数の移送をまとめる。 -/
lemma finCongr_permCongr_trans {a b c : ℕ} (h : a = b) (k : b = c)
    (σ : Equiv.Perm (Fin a)) :
    (finCongr k).permCongr ((finCongr h).permCongr σ) =
      (finCongr (h.trans k)).permCongr σ := by
  subst b
  subst c
  rfl

/-- 概要：右ブロックの長さの移送はブロック置換全体の移送と一致する（Berger–Moerdijk §1）。
方針：右ブロックの長さの等式で型を同一視する。
規約：左ブロックの長さと置換は固定する。
使われ方：尾の arity の移送を全入力の arity の移送へ移す。 -/
lemma blockEquiv_permCongr_right (a : ℕ) {b c : ℕ} (h : b = c)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv σ ((finCongr h).permCongr τ) =
      (finCongr (congrArg (a + ·) h)).permCongr (_root_.SerrePositivity.FiniteBijection.blockEquiv σ τ) := by
  subst c
  rfl

/-- 概要：左ブロックの長さの移送はブロック置換全体の移送と一致する（Berger–Moerdijk §1）。
方針：左ブロックの長さの等式で型を同一視する。
規約：右ブロックの長さと置換は固定する。
使われ方：既に連結した入力族の arity の移送を外へまとめる。 -/
lemma blockEquiv_permCongr_left {a b : ℕ} (h : a = b) (c : ℕ)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin c)) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv ((finCongr h).permCongr σ) τ =
      (finCongr (congrArg (· + c) h)).permCongr (_root_.SerrePositivity.FiniteBijection.blockEquiv σ τ) := by
  subst b
  rfl

/-- 概要：空の左ブロックを付ける置換は arity の移送に等しい（Berger–Moerdijk §1）。
方針：空のブロックと非空側のブロックの直和を右側で評価する。
規約：空のブロックには恒等置換を使う。
使われ方：入力族の長さ 0 の場合のブロック置換を簡約する。 -/
lemma blockEquiv_zero_left (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin 0)) σ =
      (finCongr (Nat.zero_add n).symm).permCongr σ := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x => exact Fin.elim0 x
  | inr x =>
    apply Fin.ext
    change (_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin 0)) σ (x.natAdd 0)).val = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd, Nat.zero_add]

/-- 概要：空の右ブロックを付ける置換は arity の移送に等しい（Berger–Moerdijk §1）。
方針：非空側のブロックと空のブロックの直和を左側で評価する。
規約：空のブロックには恒等置換を使う。
使われ方：最後の入力を分離するブロック置換の帰納法の基底を処理する。 -/
lemma blockEquiv_zero_right (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin 0)) =
      (finCongr (Nat.add_zero n).symm).permCongr σ := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x =>
    apply Fin.ext
    change (_root_.SerrePositivity.FiniteBijection.blockEquiv σ (Equiv.refl (Fin 0)) (x.castAdd 0)).val = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
    rfl
  | inr x => exact Fin.elim0 x

/-- 概要：三つのブロックの置換は括弧付けの変更と両立する（Berger–Moerdijk §1）。
方針：有限直和の全射性を使って各ブロックの入力へ分け、置換の値を比較する。
規約：左括弧の長さから右括弧の長さへの移送には自然数加法の結合則を使う。
使われ方：全入力への合成の等変性の帰納法で残りの入力ブロックをまとめ直す。 -/
lemma blockEquiv_assoc (a b c : ℕ) (α : Equiv.Perm (Fin a)) (β : Equiv.Perm (Fin b))
    (γ : Equiv.Perm (Fin c)) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.FiniteBijection.blockEquiv α β) γ =
      (finCongr (Nat.add_assoc a b c).symm).permCongr
        (_root_.SerrePositivity.FiniteBijection.blockEquiv α (_root_.SerrePositivity.FiniteBijection.blockEquiv β γ)) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x =>
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
    cases x with
    | inl x =>
      change (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.FiniteBijection.blockEquiv α β) γ)
        ((x.castAdd b).castAdd c) = _
      apply Fin.ext
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
      change (α x).val =
        (_root_.SerrePositivity.FiniteBijection.blockEquiv α (_root_.SerrePositivity.FiniteBijection.blockEquiv β γ) (x.castAdd (b + c))).val
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left]
      rfl
    | inr x =>
      change (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.FiniteBijection.blockEquiv α β) γ)
        ((x.natAdd a).castAdd c) = _
      apply Fin.ext
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
      change ((β x).natAdd a).val =
        (_root_.SerrePositivity.FiniteBijection.blockEquiv α (_root_.SerrePositivity.FiniteBijection.blockEquiv β γ)
          ((x.castAdd c).natAdd a)).val
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left]
      rfl
  | inr x =>
    change (_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.FiniteBijection.blockEquiv α β) γ)
      (x.natAdd (a + b)) = _
    apply Fin.ext
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_permCongr_val]
    have he : (⟨a + b + x.val, by omega⟩ : Fin (a + (b + c))) =
        (x.natAdd b).natAdd a := by apply Fin.ext; dsimp; omega
    simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right]
    dsimp
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
