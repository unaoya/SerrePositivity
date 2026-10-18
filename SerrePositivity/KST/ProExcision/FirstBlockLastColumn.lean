module
public import SerrePositivity.KST.ProExcision.MatrixLastColumn

/-!
# 単位ブロック和の最終座標の公式

概要：単位ブロック和を最後の補助座標で制限したときの成分を比較する。
方針：first n の添字と補助添字を分けた成分公式を使う。
規約：KST Claim 4.15、非可換な行列環。
使われ方：外部 ĜL の作用と最終列の実分解の可換性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：単位ブロック和の任意の成分の公式。
方針：二つの添字が first n に入るかで四つのブロックを評価する。
規約：KST Claim 4.15。使われ方：補助座標の制限の比較。 -/
lemma firstBlockMatrix_entry (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin (n + m)) :
    firstBlockMatrix n m M i j =
      if hi : i.val < n then if hj : j.val < n then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if i = j then 1 else 0 := by
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [finSumFinEquiv_apply_left, firstBlockMatrix_left_left]
    | inr j =>
      simp [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        firstBlockMatrix_left_right]
  | inr i =>
    cases j with
    | inl j =>
      have hn : Fin.natAdd n i ≠ Fin.castAdd m j := by
        intro h
        have hv := congrArg Fin.val h
        have hj := j.isLt
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      simp [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        firstBlockMatrix_right_left, hn]
    | inr j =>
      simp [finSumFinEquiv_apply_right, firstBlockMatrix_right_right, Matrix.one_apply]

/-- 概要：最後の補助行は恒等行。
方針：last は first n の範囲外であることを成分公式へ適用する。
規約：KST Claim 4.15。使われ方：ブロックの積の公式への入力。 -/
lemma firstBlockMatrix_lastRow (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (j : Fin (n + m + 1)) :
    firstBlockMatrix n (m + 1) M (Fin.last (n + m)) j =
      (1 : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) (Fin.last (n + m)) j := by
  rw [firstBlockMatrix_entry, dif_neg (by simp only [Fin.val_last]; omega)]
  rfl

/-- 概要：単位ブロック和の最終列の前半は零。
方針：最後の補助列の非対角成分を計算する。
規約：KST Claim 4.15。使われ方：最終列の作用の公式。 -/
lemma firstBlockMatrix_lastColumn (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    matrixLastColumn (firstBlockMatrix n (m + 1) M) = 0 := by
  funext i
  change firstBlockMatrix n (m + 1) M i.castSucc (Fin.last (n + m)) = 0
  rw [firstBlockMatrix_entry]
  have hl : (Fin.last (n + m)).val = n + m := rfl
  split_ifs with hi hj he
  · exfalso
    omega
  · rfl
  · exact False.elim (Fin.castSucc_ne_last i he)
  · rfl

/-- 概要：単位ブロック和の左上ブロックは補助 rank を一つ減らしたもの。
方針：castSucc は添字の値と等号を保つことを成分公式へ適用する。
規約：KST Claim 4.15。使われ方：三角群の分解の基底作用の比較。 -/
lemma firstBlockMatrix_dropLast (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    matrixDropLast (firstBlockMatrix n (m + 1) M) = firstBlockMatrix n m M := by
  apply Matrix.ext
  intro i j
  change firstBlockMatrix n (m + 1) M i.castSucc j.castSucc = firstBlockMatrix n m M i j
  rw [firstBlockMatrix_entry, firstBlockMatrix_entry]
  simp only [Fin.val_castSucc, Fin.castSucc_inj]

end SerrePositivity.KST.ProExcision
