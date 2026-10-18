module
public import SerrePositivity.KST.ProExcision.FirstBlockLastColumn
public import SerrePositivity.KST.ProExcision.SimplicialColumnBlockInclusion

/-!
# 単位ブロック和と列の安定化の合成則

概要：補助 rank を一つずつ増やす安定化と、一度に増やす実射を比較する。
方針：列の零埋めと行列のブロック和を任意の成分で計算する。
規約：KST Claim 4.15 から Proposition 4.14 への安定化。
使われ方：十分大きい有限 rank の零写像を実順序列の遷移へ同定する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision

/-- 概要：補助 rank 零の列のブロック包含は恒等。
方針：全ての添字は元の範囲内である。
規約：KST Claim 4.15 の rank の基底。使われ方：反復安定化の基底。 -/
lemma columnBlockInclusion_zero (A : Type u) [AddCommGroup A] (n : ℕ) (v : Fin n → A) :
    columnBlockInclusion A n 0 v = v := by
  funext i
  simp [columnBlockInclusion]

/-- 概要：列の零埋めを一座標追加すると補助 rank を一つ増やした零埋めに一致する。
方針：添字が n 未満・n+m 未満かで分ける。
規約：KST Proposition 4.14 の通常の安定化。
使われ方：順序列の遷移と Claim 4.15 の実列の同定。 -/
lemma columnBlockInclusion_succ (A : Type u) [AddCommGroup A] (n m : ℕ) (v : Fin n → A) :
    columnBlockInclusion A (n + m) 1 (columnBlockInclusion A n m v) =
      columnBlockInclusion A n (m + 1) v := by
  funext i
  dsimp only [columnBlockInclusion, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> first | rfl | omega

/-- 概要：補助 rank 零の単位ブロック和は元の行列。
方針：全ての添字が first n に入ることを成分公式へ適用する。
規約：KST Proposition 4.14。使われ方：反復安定化の基底。 -/
lemma firstBlockMatrix_zero {R : Type u} [Ring R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    firstBlockMatrix n 0 M = M := by
  apply Matrix.ext
  intro i j
  rw [firstBlockMatrix_entry]
  simp [i.isLt, j.isLt]

/-- 概要：単位ブロック和に一座標を追加すると補助 rank を一つ増やしたものに一致する。
方針：成分公式を二度使い、添字の範囲で分ける。
規約：KST Proposition 4.14、非可換な係数環。
使われ方：有限 rank の遷移と通常のブロック和の同定。 -/
lemma firstBlockMatrix_succ {R : Type u} [Ring R] (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    firstBlockMatrix (n + m) 1 (firstBlockMatrix n m M) = firstBlockMatrix n (m + 1) M := by
  apply Matrix.ext
  intro i j
  simp only [firstBlockMatrix_entry]
  split_ifs <;> grind [Fin.ext_iff]

end SerrePositivity.KST.ProExcision
