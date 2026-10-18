module
public import SerrePositivity.KST.ProExcision.AffineMatrixAction

/-!
# 外部行列作用と補助座標挿入の可換性

概要：first n 行の外に恒等座標を挿入すると、行列のアフィン作用と可換になる。
方針：指定点と既存座標に分け、既存の前半行と後半行を各成分で比較する。
規約：KST Lemma 4.16 の P の埋め込みの同変性。
使われ方：μ の第一因子と外部行列作用を接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：first n 行以後への挿入では前半の既存行の添字は不変。
方針：指定点の手前の succAbove は castSucc。
規約：KST 4.16。使われ方：外部作用の有限和の添字を合わせる。 -/
lemma insertion_preserves_firstRows (n m : ℕ) (p : Fin (n + m + 1)) (hp : n ≤ p.val) (i : Fin n) :
    p.succAbove (Fin.castAdd m i) = Fin.castAdd (m + 1) i := by
  have hi : (Fin.castAdd m i).castSucc < p := by
    change i.val < p.val
    exact i.isLt.trans_le hp
  rw [Fin.succAbove_of_castSucc_lt _ _ hi]
  apply Fin.ext
  rfl

/-- 概要：挿入した補助列は恒等行列の列。
方針：指定点と既存成分で対角と交差零の公式を使う。
規約：KST 4.16。使われ方：外部作用で追加列が変わらないことの確認。 -/
lemma matrixInsertion_fixed_new_column {N : ℕ} (p : Fin (N + 1))
    (A : Matrix (Fin N) (Fin N) R) (i : Fin (N + 1)) :
    matrixInsertionHom p A i p = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) R) i p := by
  obtain ⟨i, rfl⟩ := (finSuccEquiv' p).symm.surjective i
  cases i <;> simp [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some,
    matrixInsertion_self, matrixInsertion_column, Matrix.one_apply]

/-- 概要：アフィン行列作用と補助恒等座標の挿入は可換。
方針：既存の前半行の有限和と後半行の不変性、追加行・列の固定性を使う。
規約：KST Lemma 4.16 の非可換版、挿入は first n 行の外。
使われ方：実三角ブロック群の埋め込みの全行列同変性。 -/
lemma affineMatrixAction_insertion (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (p : Fin (n + m + 1)) (hp : n ≤ p.val)
    (A : Matrix (Fin (n + m)) (Fin (n + m)) R) :
    matrixInsertionHom p (affineMatrixAction n m M A) =
      affineMatrixAction n (m + 1) M (matrixInsertionHom p A) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSuccEquiv' p).symm.surjective i
  obtain ⟨j, rfl⟩ := (finSuccEquiv' p).symm.surjective j
  cases i with
  | none =>
    cases j <;> simp only [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some]
    · rw [affineMatrixAction_otherRows n (m + 1) M _ p p hp, matrixInsertion_self, matrixInsertion_self]
    · rw [affineMatrixAction_otherRows n (m + 1) M _ p _ hp, matrixInsertion_row, matrixInsertion_row]
  | some i =>
    cases j with
    | none =>
      simp only [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some]
      rw [matrixInsertion_column, affineMatrixAction_fixed_column n (m + 1) M _ p
        (matrixInsertion_fixed_new_column p A)]
      simp [Matrix.one_apply]
    | some j =>
      simp only [finSuccEquiv'_symm_some]
      rw [matrixInsertion_succAbove]
      by_cases hi : i.val < n
      · let i₀ : Fin n := ⟨i.val, hi⟩
        have hs : Fin.castAdd m i₀ = i := Fin.ext rfl
        rw [← hs, insertion_preserves_firstRows n m p hp i₀,
          affineMatrixAction_firstRows, affineMatrixAction_firstRows]
        have hid : (1 : Matrix (Fin (n + (m + 1))) (Fin (n + (m + 1))) R)
            (Fin.castAdd (m + 1) i₀) (p.succAbove j) =
            (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) (Fin.castAdd m i₀) j := by
          rw [← insertion_preserves_firstRows n m p hp i₀]
          simp only [Matrix.one_apply, Fin.succAbove_right_injective.eq_iff]
        rw [hid]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [← insertion_preserves_firstRows n m p hp k, matrixInsertion_difference_succAbove]
      · have hs : n ≤ i.val := Nat.le_of_not_gt hi
        have ht : n ≤ (p.succAbove i).val := hs.trans (insertion_index_le p i)
        rw [affineMatrixAction_otherRows n m M _ i j hs,
          affineMatrixAction_otherRows n (m + 1) M _ _ _ ht, matrixInsertion_succAbove]

/-- 概要：実三角ブロック群の挿入は全行列作用に同変。
方針：単位と部分群の外延性からアフィン公式の可換性を使う。
規約：KST Lemma 4.16、μ の第一因子 P→H。
使われ方：A.5 の実データの外部 G 同変性を証明する。 -/
lemma triangularBlockInsertion_equivariant (n m : ℕ) (J : TwoSidedIdeal R)
    (p : Fin (n + m + 1)) (hp : n ≤ p.val) (M : Matrix (Fin n) (Fin n) R)
    (g : triangularBlockGroup n m J) :
    triangularBlockGroupInsertion n m J p (triangularBlockMatrixAction n m J M g) =
      triangularBlockMatrixAction n (m + 1) J M (triangularBlockGroupInsertion n m J p g) := by
  apply Subtype.ext
  apply Units.ext
  change matrixInsertionHom p ((triangularBlockMatrixEnd n m J M g).val :
    Matrix (Fin (n + m)) (Fin (n + m)) R) =
    ((triangularBlockMatrixEnd n (m + 1) J M (triangularBlockGroupInsertion n m J p g)).val :
      Matrix (Fin (n + (m + 1))) (Fin (n + (m + 1))) R)
  rw [triangularBlockMatrixEnd_val, triangularBlockMatrixEnd_val]
  exact affineMatrixAction_insertion n m M p hp (g.val : Matrix (Fin (n + m)) (Fin (n + m)) R)

end SerrePositivity.KST.ProExcision
