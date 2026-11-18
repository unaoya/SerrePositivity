module

public import SerrePositivity.GroupTheory.Coxeter.FirstToLast

/-!
模型。文献の定義との比較は後で
# 最後の隣接互換の入力位置

概要：Berger–Moerdijk §1 の末尾二入力の交換に用いる隣接互換を各位置で計算する。
方針：最後の隣接互換を二点の互換として評価する。
規約：n+2 入力の最後の二位置は last n の castSucc と last (n+1)。
使われ方：末尾二因子の分離後の対象を、前半と交換した二因子に同定する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.SerrePositivity.Coxeter

/-- 概要：最後の隣接互換は前半の n 入力を固定する（Berger–Moerdijk §1）。
方針：前半の位置は交換する二点より小さいことを使う。
規約：前半は二回の castSucc で指定する。
使われ方：末尾交換後にも前半の有限テンソル族が保たれることを示す。 -/
lemma adjacentLast_prefix (n : ℕ) (i : Fin n) :
    adjacentTransposition (Fin.last n) i.castSucc.castSucc = i.castSucc.castSucc := by
  change Equiv.swap (Fin.last n).castSucc (Fin.last n).succ i.castSucc.castSucc = _
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    have := i.isLt
    omega
  · intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    have := i.isLt
    omega

/-- 概要：最後の隣接互換は最後から二番目を最後へ送る（Berger–Moerdijk §1）。
方針：二点の互換の左側の値を使う。
規約：最後から二番目は last n の castSucc。
使われ方：末尾交換後の二因子の順序を計算する。 -/
lemma adjacentLast_penultimate (n : ℕ) :
    adjacentTransposition (Fin.last n) (Fin.last n).castSucc = Fin.last (n + 1) := by
  change Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).castSucc = _
  rw [Equiv.swap_apply_left]
  rfl

/-- 概要：最後の隣接互換は最後を最後から二番目へ送る（Berger–Moerdijk §1）。
方針：二点の互換の右側の値を使う。
規約：最後は last (n+1)。
使われ方：末尾交換後の二因子の順序を計算する。 -/
lemma adjacentLast_last (n : ℕ) :
    adjacentTransposition (Fin.last n) (Fin.last (n + 1)) = (Fin.last n).castSucc := by
  change Equiv.swap (Fin.last n).castSucc (Fin.last n).succ (Fin.last n).succ = _
  exact Equiv.swap_apply_right _ _

/-- 概要：一つ長い族の最後の隣接互換は尾の最後の隣接互換をずらしたものである（Berger–Moerdijk §1）。
方針：既存の隣接互換をずらす計算則を最後の位置へ適用する。
規約：先頭の位置は固定する。
使われ方：末尾二因子の交換の帰納法で尾の族へ移る。 -/
lemma adjacentLast_succ (n : ℕ) (i : Fin (n + 2)) :
    adjacentTransposition (Fin.last (n + 1)) i.succ =
      (adjacentTransposition (Fin.last n) i).succ := by
  have h := shiftPerm_succ (adjacentTransposition (Fin.last n)) i
  rw [shiftPerm_adjacent (n + 1) (Fin.last n)] at h
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
