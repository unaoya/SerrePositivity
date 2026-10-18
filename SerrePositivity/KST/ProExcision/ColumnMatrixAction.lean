module
public import SerrePositivity.KST.ProExcision.IdealMatrixAction

/-!
# first n 行の補助列への実行列作用

概要：補助列への diag(M,1) の左積は列ベクトルへの M の左積と一致する。
方針：first n 行と残りの行で実列を評価する。
規約：KST Lemma 4.16 の ψ・φ の行列同変性。
使われ方：イデアル内の実列の群準同型が外部行列作用と可換であることの証明。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
open scoped Matrix
variable {R : Type u} [Ring R]

/-- 概要：first n 行に入れた補助列の既存の各行の成分。
方針：単一成分行列の和を一つの行で評価する。
規約：KST 4.16。使われ方：列の左行列作用の計算。 -/
lemma firstRows_blockColumn_apply (n m : ℕ) (q : Fin (n + m)) (v : Fin n → R)
    (i : Fin n) (j : Fin (n + m)) :
    blockColumn (Fin.castAdd m) q v (Fin.castAdd m i) j = if q = j then v i else 0 := by
  by_cases h : q = j
  · subst j
    simp [blockColumn, Matrix.sum_apply, Matrix.single_apply]
  · simp [blockColumn, Matrix.sum_apply, Matrix.single_apply, h]

/-- 概要：first n 行に入れた補助列の残りの行は零。
方針：前半の行と後半の行の添字が一致しないことを使う。
規約：KST 4.16。使われ方：補助座標の作用による不変性。 -/
lemma otherRows_blockColumn_apply (n m : ℕ) (q : Fin (n + m)) (v : Fin n → R)
    (i : Fin m) (j : Fin (n + m)) : blockColumn (Fin.castAdd m) q v (Fin.natAdd n i) j = 0 := by
  have h : ∀ k : Fin n, Fin.castAdd m k ≠ Fin.natAdd n i := by
    intro k hk
    have hv := congrArg Fin.val hk
    change k.val = n + i.val at hv
    have hb := k.isLt
    omega
  simp [blockColumn, Matrix.sum_apply, Matrix.single_apply, h]

/-- 概要：実補助列への左ブロック行列の作用は列ベクトルの左行列積。
方針：前半の行では有限和を評価し、後半の行は零であることを使う。
規約：KST Lemma 4.16、非可換係数と全行列。
使われ方：Q→H の ψ と φ の同変性。 -/
lemma firstBlockMatrix_mul_blockColumn (n m : ℕ) (M : Matrix (Fin n) (Fin n) R)
    (q : Fin (n + m)) (v : Fin n → R) :
    firstBlockMatrix n m M * blockColumn (Fin.castAdd m) q v =
      blockColumn (Fin.castAdd m) q (M *ᵥ v) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i =>
    simp only [finSumFinEquiv_apply_left]
    rw [firstBlockMatrix_mul_firstRows, firstRows_blockColumn_apply]
    by_cases h : q = j <;> simp [firstRows_blockColumn_apply, h, Matrix.mulVec_apply_eq_sum]
  | inr i =>
    simp only [finSumFinEquiv_apply_right]
    rw [firstBlockMatrix_mul_otherRows, otherRows_blockColumn_apply, otherRows_blockColumn_apply]

end SerrePositivity.KST.ProExcision
