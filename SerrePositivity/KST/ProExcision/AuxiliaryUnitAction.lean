module
public import SerrePositivity.KST.ProExcision.MatrixActionComponents

/-!
# 共役の補助元 u の全行列作用による固定性

概要：first n 行への行列作用は Lemma 4.16 の補助元 u を固定する。
方針：diag(M,1) は補助列で恒等なので U の左積は U 自身。
規約：KST Lemma 4.16 と Construction A.6、I の可換性を用いない。
使われ方：A.6 の実共役ホモトピーの外部行列同変性。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：diag(M,1) は補助座標の列では恒等行列。
方針：列が後半に属することから、左上・右下の成分の公式を使う。
規約：KST 4.16。使われ方：補助元 U の左積による固定性。 -/
lemma firstBlockMatrix_fixed_aux_column (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (j : Fin (n + m)) (hj : n ≤ j.val) (i : Fin (n + m)) :
    firstBlockMatrix n m M i j = (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) i j := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective j
  cases j with
  | inl j =>
    simp only [finSumFinEquiv_apply_left] at hj
    have h := j.isLt
    change n ≤ j.val at hj
    omega
  | inr j =>
    simp only [finSumFinEquiv_apply_right]
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
    cases i with
    | inl i =>
      have hne : Fin.castAdd m i ≠ Fin.natAdd n j := by
        intro h
        have hv := congrArg Fin.val h
        change i.val = n + j.val at hv
        have hi := i.isLt
        omega
      simp [finSumFinEquiv_apply_left, firstBlockMatrix_left_right, Matrix.one_apply, hne]
    | inr i =>
      simp [finSumFinEquiv_apply_right, firstBlockMatrix_right_right, Matrix.one_apply]

/-- 概要：Lemma 4.16 の実補助元 u は全行列作用で固定される。
方針：作用の値を実成分で展開し、補助列の固定性を単一成分行列の左積へ適用する。
規約：KST 4.16・A.6、一般の非可逆行列と非可換な係数。
使われ方：共役の実ホモトピーを外部行列同変なまま用いる。 -/
lemma auxiliaryBlockUnit_fixed (n m : ℕ) (J : TwoSidedIdeal R) (a : J)
    (M : Matrix (Fin n) (Fin n) R) :
    triangularBlockMatrixAction n (m + 2) J M (auxiliaryBlockUnit n m J a) = auxiliaryBlockUnit n m J a := by
  apply Subtype.ext
  apply Units.ext
  change ((triangularBlockMatrixEnd n (m + 2) J M (auxiliaryBlockUnit n m J a)).val :
    Matrix (Fin (n + (m + 2))) (Fin (n + (m + 2))) R) = _
  rw [triangularBlockMatrixEnd_val]
  change 1 + firstBlockMatrix n (m + 2) M *
    (1 + Matrix.single (auxiliaryBlockIndex n m) (Fin.last (n + m + 1)) (a : R) - 1) =
      1 + Matrix.single (auxiliaryBlockIndex n m) (Fin.last (n + m + 1)) (a : R)
  rw [add_sub_cancel_left]
  congr 1
  apply matrix_mul_single_of_fixed_column
  exact firstBlockMatrix_fixed_aux_column n (m + 2) M (auxiliaryBlockIndex n m)
    (by change n ≤ n + m; omega)

end SerrePositivity.KST.ProExcision
