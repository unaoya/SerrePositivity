module

public import SerrePositivity.GroupTheory.Coxeter.FirstToLast

/-!
模型。文献の定義との比較は後で
# 末尾を固定する隣接互換の入力位置

概要：Berger–Moerdijk §1 の反復合成の帰納法で、前半の隣接互換を末尾を固定して持ち上げる。
方針：既存の置換の持ち上げと隣接互換の計算則を使う。
規約：前半の位置を castSucc で埋め込む。
使われ方：末尾以外の隣接交換を最後の因子の分離の前後で比較する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.SerrePositivity.Coxeter

/-- 概要：末尾を固定して持ち上げた隣接互換は前半の位置で元の互換に一致する（Berger–Moerdijk §1）。
方針：置換の持ち上げの castSucc 上の計算則を適用する。
規約：元の隣接互換は n+1 入力に作用する。
使われ方：交換後の族の前半を元の前半の交換として記述する。 -/
lemma adjacentCastSucc_prefix (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    adjacentTransposition i.castSucc j.castSucc = (adjacentTransposition i j).castSucc := by
  have h := permLift_apply_castSucc (n + 1) (adjacentTransposition i) j
  rw [permLift_adjacent n i] at h
  exact h

/-- 概要：前半の隣接互換を持ち上げた互換は最後の位置を固定する（Berger–Moerdijk §1）。
方針：置換の持ち上げの最後の位置での計算則を適用する。
規約：持ち上げ後は n+2 入力に作用する。
使われ方：最後の因子が交換の前後で変わらないことを示す。 -/
lemma adjacentCastSucc_last (n : ℕ) (i : Fin n) :
    adjacentTransposition i.castSucc (Fin.last (n + 1)) = Fin.last (n + 1) := by
  have h := permLift_apply_last (n + 1) (adjacentTransposition i)
  rw [permLift_adjacent n i] at h
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
