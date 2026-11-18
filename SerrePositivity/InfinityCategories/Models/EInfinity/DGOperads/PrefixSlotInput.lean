module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.PrefixSlotPermutations
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AdjacentCastSucc

/-!
模型。文献の定義との比較は後で
# 反復代入の始域における前半の置換

概要：Berger–Moerdijk §1 の反復代入の始域で、前半の置換と挿入位置、未代入の尾を分ける。
方針：前半の置換を挿入位置を固定して持ち上げ、尾の恒等置換と連結する。
規約：元の始域の arity は (a+1)+b。
使われ方：位置 a への代入の前後の外側等変性を arity の移送に通す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.SerrePositivity.Coxeter

/-- 概要：前半 a 入力を置換し挿入位置と未代入の尾 b 入力を固定する（Berger–Moerdijk §1）。
方針：末尾を固定した置換の持ち上げと尾の恒等置換のブロック和を使う。
規約：対象の arity は (a+1)+b。
使われ方：反復代入の再帰の最初の部分合成の始域に作用する。 -/
noncomputable def operadPrefixInputPermutation (a b : ℕ) (σ : Equiv.Perm (Fin a)) :
    Equiv.Perm (Fin ((a + 1) + b)) :=
  _root_.SerrePositivity.FiniteBijection.blockEquiv (permLift a σ) (Equiv.refl (Fin b))

/-- 概要：反復代入の始域の前半には元の置換が作用する（Berger–Moerdijk §1）。
方針：ブロック和の左側と持ち上げた置換の前半での値を計算する。
規約：前半の位置を j.val で指定する。
使われ方：arity の括弧の移送の前後で前半の置換を比較する。 -/
lemma operadPrefixInputPermutation_prefix (a b : ℕ) (σ : Equiv.Perm (Fin a)) (j : Fin a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ ⟨j.val, by omega⟩ =
      ⟨(σ j).val, by have := (σ j).isLt; omega⟩ := by
  apply Fin.ext
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv (permLift a σ) (Equiv.refl (Fin b))
    (j.castSucc.castAdd b)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, permLift_apply_castSucc]
  rfl

/-- 概要：反復代入の始域の前半の置換は挿入位置を固定する（Berger–Moerdijk §1）。
方針：ブロック和の左側で持ち上げた置換の最後の位置の値を使う。
規約：挿入位置は a。
使われ方：外側等変性で部分合成の入力位置を変えずに保つ。 -/
lemma operadPrefixInputPermutation_slot (a b : ℕ) (σ : Equiv.Perm (Fin a)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ ⟨a, by omega⟩ = ⟨a, by omega⟩ := by
  apply Fin.ext
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv (permLift a σ) (Equiv.refl (Fin b))
    ((Fin.last a).castAdd b)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_left, permLift_apply_last]
  rfl

/-- 概要：反復代入の始域の前半の置換は元の未代入の尾を固定する（Berger–Moerdijk §1）。
方針：ブロック和の右側の恒等置換の値を使う。
規約：尾の位置を a+1+j.val で指定する。
使われ方：arity の移送の前後で未代入の尾を比較する。 -/
lemma operadPrefixInputPermutation_after (a b : ℕ) (σ : Equiv.Perm (Fin a)) (j : Fin b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ ⟨a + 1 + j.val, by omega⟩ =
      ⟨a + 1 + j.val, by omega⟩ := by
  apply Fin.ext
  change (_root_.SerrePositivity.FiniteBijection.blockEquiv (permLift a σ) (Equiv.refl (Fin b))
    (j.natAdd (a + 1))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_apply_right]
  rfl

/-- 概要：反復代入の始域の前半の置換は挿入位置と尾をまとめた右側を固定する（Berger–Moerdijk §1）。
方針：右側の最初の位置と残りの位置に分ける。
規約：右側の長さは b+1。
使われ方：前半と右側の二つの区間で arity の移送を比較する。 -/
lemma operadPrefixInputPermutation_suffix (a b : ℕ) (σ : Equiv.Perm (Fin a))
    (j : Fin (b + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ ⟨a + j.val, by omega⟩ = ⟨a + j.val, by omega⟩ := by
  by_cases hj : j.val = 0
  · have he : (⟨a + j.val, by omega⟩ : Fin (a + 1 + b)) = ⟨a, by omega⟩ := by
      apply Fin.ext
      change a + j.val = a
      omega
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation_slot]
  · let t : Fin b := ⟨j.val - 1, by omega⟩
    have he : (⟨a + j.val, by omega⟩ : Fin (a + 1 + b)) =
        ⟨a + 1 + t.val, by omega⟩ := by apply Fin.ext; dsimp [t]; omega
    rw [he, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation_after]

private lemma finCongr_prefix_input_val {r s : ℕ} (h : r = s)
    (σ : Equiv.Perm (Fin r)) (x : Fin s) :
    (((finCongr h).permCongr σ) x).val = (σ ⟨x.val, by omega⟩).val := by
  subst s
  rfl

/-- 概要：始域の前半の置換は部分合成の arity の括弧へ移すと前半のブロック置換となる（Berger–Moerdijk §1）。
方針：arity の移送が位置の値を保つことを使い、前半と右側で値を比較する。
規約：移送後の arity は a+b+1。
使われ方：反復代入の始域の置換作用を部分合成の外側等変性へ適用する。 -/
lemma operadPrefixInputPermutation_index (a b : ℕ) (σ : Equiv.Perm (Fin a)) :
    (finCongr (by omega : a + 1 + b = a + b + 1)).permCongr
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.finCongr_prefix_input_val]
  by_cases hx : x.val < a
  · let j : Fin a := ⟨x.val, hx⟩
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation a b σ ⟨j.val, by omega⟩).val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ ⟨j.val, by omega⟩).val
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation_prefix, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_prefix]
  · let j : Fin (b + 1) := ⟨x.val - a, by omega⟩
    have hs : (⟨x.val, by omega⟩ : Fin (a + 1 + b)) =
        ⟨a + j.val, by omega⟩ := by apply Fin.ext; dsimp [j]; omega
    have ht : x = (⟨a + j.val, by omega⟩ : Fin (a + b + 1)) := by
      apply Fin.ext
      dsimp [j]
      omega
    rw [hs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixInputPermutation_suffix]
    exact (congrArg Fin.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation_suffix a b 1 σ j)).symm.trans
      (congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadPrefixPermutation a b 1 σ z).val) ht).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
