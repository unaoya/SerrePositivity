module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.BinarySlotSwap
public import SerrePositivity.GroupTheory.Coxeter.FirstToLast

/-!
模型。文献の定義との比較は後で
# 入力ブロックの交換の再帰

概要：Berger–Moerdijk §1 の入力ブロックの交換を、小さいブロックの交換と一入力の移動へ分解する。
方針：先頭の一入力を固定して残りのブロックを交換し、先頭の入力を交換後の右ブロックへ移す。
規約：長さの括弧付けの違いは Fin の標準同値で移送する。
使われ方：テンソル冪の連結とブロック交換の両立を帰納的に証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.SerrePositivity.Coxeter

/-- 概要：ブロック全単射の左入力の値を与える（Berger–Moerdijk §1）。
方針：有限直和の左成分で全単射を計算する。
規約：左右それぞれの始域と終域の長さの式は異なってよい。
使われ方：異なる長さの式を持つブロック交換の再帰を計算する。 -/
lemma blockEquiv_map_left {m n m' n' : ℕ} (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n')
    (j : Fin m) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv e f (j.castAdd n) = (e j).castAdd n' := by
  change _root_.SerrePositivity.FiniteBijection.blockEquiv e f (finSumFinEquiv (Sum.inl j)) = _
  simp [_root_.SerrePositivity.FiniteBijection.blockEquiv]

/-- 概要：ブロック全単射の右入力の値を与える（Berger–Moerdijk §1）。
方針：有限直和の右成分で全単射を計算する。
規約：終域の左ブロックの長さだけ入力位置を平行移動する。
使われ方：異なる長さの式を持つブロック交換の再帰を計算する。 -/
lemma blockEquiv_map_right {m n m' n' : ℕ} (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n')
    (j : Fin n) :
    _root_.SerrePositivity.FiniteBijection.blockEquiv e f (j.natAdd m) = (f j).natAdd m' := by
  change _root_.SerrePositivity.FiniteBijection.blockEquiv e f (finSumFinEquiv (Sum.inr j)) = _
  simp [_root_.SerrePositivity.FiniteBijection.blockEquiv]

/-- 概要：空の左ブロックの交換は長さの式の移送である（Berger–Moerdijk §1）。
方針：有限直和の右側の入力で値を比較する。
規約：左ブロックの長さは 0。
使われ方：ブロック交換の帰納法の基底を処理する。 -/
lemma operadBlockSwap_zero (b : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap 0 b = finCongr (by omega : 0 + b = b + 0) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x => exact Fin.elim0 x
  | inr x =>
    simp only [finSumFinEquiv_apply_right]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
    apply Fin.ext
    dsimp
    omega

/-- 概要：一入力とブロックの交換は先頭を末尾へ送る巡回置換である（Berger–Moerdijk §1）。
方針：先頭と残りの位置で、ブロック交換と既存の巡回置換の値を比較する。
規約：長さ 1+b から b+1 への移送を先に行う。
使われ方：一入力の移動のテンソル冪の作用を既存の braiding の計算則に接続する。 -/
lemma operadBlockSwap_one (b : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap 1 b = (finCongr (by omega : 1 + b = b + 1)).trans (firstToLastPerm b) := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x =>
    simp only [finSumFinEquiv_apply_left]
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap 1 b ((0 : Fin 1).castAdd b) = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
    have he : finCongr (by omega : 1 + b = b + 1) ((0 : Fin 1).castAdd b) = 0 := by
      apply Fin.ext
      rfl
    simp only [Equiv.trans_apply, he, firstToLastPerm_zero]
    rfl
  | inr x =>
    simp only [finSumFinEquiv_apply_right]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
    have he : finCongr (by omega : 1 + b = b + 1) (x.natAdd 1) = x.succ := by
      apply Fin.ext
      dsimp
      omega
    simp only [Equiv.trans_apply, he, firstToLastPerm_succ]
    rfl

/-- 概要：左ブロックの長さを一つ増やした交換を二段の交換で構成する（Berger–Moerdijk §1）。
方針：先頭を固定して残りを交換し、その先頭を長さ b のブロックの後へ移す。
規約：各段の括弧付けを Fin の標準同値で移す。
使われ方：テンソル冪のブロック交換の帰納段階を記述する。 -/
def operadBlockSwapSucc (a b : ℕ) : Fin ((a + 1) + b) ≃ Fin (b + (a + 1)) :=
  (finCongr (by omega : (a + 1) + b = 1 + (a + b))).trans
    ((_root_.SerrePositivity.FiniteBijection.blockEquiv (Equiv.refl (Fin 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap a b)).trans
      ((finCongr (by omega : 1 + (b + a) = (1 + b) + a)).trans
        ((_root_.SerrePositivity.FiniteBijection.blockEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap 1 b) (Equiv.refl (Fin a))).trans
          (finCongr (by omega : (b + 1) + a = b + (a + 1))))))

/-- 概要：二段の交換は左ブロックを一つ増やした通常のブロック交換に一致する（Berger–Moerdijk §1）。
方針：先頭、左ブロックの残り、右ブロックの各入力に分けて値を比較する。
規約：零長の残りのブロックも許す。
使われ方：braiding の hexagon に対応する有限全単射の再帰を与える。 -/
lemma operadBlockSwap_succ (a b : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapSucc a b = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap (a + 1) b := by
  apply Equiv.ext
  intro x
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  cases x with
  | inl x =>
    simp only [finSumFinEquiv_apply_left]
    refine Fin.cases ?_ (fun j => ?_) x
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
      have h₀ : finCongr (by omega : (a + 1) + b = 1 + (a + b))
          ((0 : Fin (a + 1)).castAdd b) = (0 : Fin 1).castAdd (a + b) := by
        apply Fin.ext; rfl
      have h₁ : finCongr (by omega : 1 + (b + a) = (1 + b) + a)
          ((0 : Fin 1).castAdd (b + a)) = ((0 : Fin 1).castAdd b).castAdd a := by
        apply Fin.ext; rfl
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapSucc, Equiv.trans_apply]
      rw [h₀, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, Equiv.refl_apply, h₁,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
      apply Fin.ext
      rfl
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left]
      have h₀ : finCongr (by omega : (a + 1) + b = 1 + (a + b))
          (j.succ.castAdd b) = (j.castAdd b).natAdd 1 := by apply Fin.ext; dsimp; omega
      have h₁ : finCongr (by omega : 1 + (b + a) = (1 + b) + a)
          ((j.natAdd b).natAdd 1) = j.natAdd (1 + b) := by apply Fin.ext; dsimp; omega
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapSucc, Equiv.trans_apply]
      rw [h₀, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_left, h₁, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right]
      apply Fin.ext
      dsimp
      omega
  | inr x =>
    simp only [finSumFinEquiv_apply_right]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
    have h₀ : finCongr (by omega : (a + 1) + b = 1 + (a + b))
        (x.natAdd (a + 1)) = (x.natAdd a).natAdd 1 := by apply Fin.ext; dsimp; omega
    have h₁ : finCongr (by omega : 1 + (b + a) = (1 + b) + a)
        ((x.castAdd a).natAdd 1) = (x.natAdd 1).castAdd a := by apply Fin.ext; rfl
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwapSucc, Equiv.trans_apply]
    rw [h₀, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_right, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right, h₁,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.blockEquiv_map_left, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadBlockSwap_right]
    apply Fin.ext
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
