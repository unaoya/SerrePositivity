module
public import SerrePositivity.KST.ProExcision.FirstBlockMultiplication

/-!
# 三角部分環と実群上の左行列作用

概要：diag(M,1) の左乗法は三角部分環を保ち、その元に右から作用しても変わらない。
方針：first n 行では係数イデアル内の有限線形結合を使い、残りの行は不変とする。
規約：KST Lemma 4.16、一般の非可逆行列 M に対する作用。
使われ方：実ブロック群の自己準同型と外部行列モノイド作用の構成。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：三角部分環の元は diag(M,1) による右積で不変。
方針：first n 列の零性を実ブロック行列の右吸収の公式へ渡す。
規約：KST 4.16。使われ方：左乗法の乗法保存。 -/
lemma blockPattern_firstBlock_right_absorbed (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin (n + m)) (Fin (n + m)) R) (hX : X ∈ blockPatternSubring (n + m) n J) :
    X * firstBlockMatrix n m M = X := by
  apply firstBlockMatrix_right_absorbed n m M X
  intro i k
  apply hX.1 i (Fin.castAdd m k)
  change ¬ (i.val < k.val ∧ n ≤ k.val)
  have hk := k.isLt
  omega

/-- 概要：diag(M,1) の左乗法は係数付き三角部分環を保つ。
方針：first n 行はイデアル内の線形結合、残りの行は同じ成分とする。
規約：KST 4.16、I の可換性は不要。
使われ方：一般の行列の作用を実群に持ち上げるための所属条件。 -/
lemma blockPattern_firstBlock_left_mem (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin (n + m)) (Fin (n + m)) R) (hX : X ∈ blockPatternSubring (n + m) n J) :
    firstBlockMatrix n m M * X ∈ blockPatternSubring (n + m) n J := by
  constructor
  · intro i j hij
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
    cases i with
    | inl i =>
      simp only [finSumFinEquiv_apply_left] at hij ⊢
      rw [firstBlockMatrix_mul_firstRows]
      have hj : j.val < n := by
        change ¬ (i.val < j.val ∧ n ≤ j.val) at hij
        have hi := i.isLt
        omega
      apply Finset.sum_eq_zero
      intro k _
      have hz : X (Fin.castAdd m k) j = 0 := hX.1 _ _ (by
        intro h
        exact (Nat.not_le_of_gt hj) h.2)
      rw [hz, mul_zero]
    | inr i =>
      simp only [finSumFinEquiv_apply_right] at hij ⊢
      rw [firstBlockMatrix_mul_otherRows]
      exact hX.1 _ _ hij
  · intro i j
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
    cases i with
    | inl i =>
      simp only [finSumFinEquiv_apply_left]
      rw [firstBlockMatrix_mul_firstRows]
      exact J.finsetSum_mem _ _ (fun k _ ↦ J.mul_mem_left _ _ (hX.2 _ _))
    | inr i =>
      simp only [finSumFinEquiv_apply_right]
      rw [firstBlockMatrix_mul_otherRows]
      exact hX.2 _ _

/-- 概要：一般の行列 M による実三角ブロック群の自己準同型。
方針：三角部分環上の左乗法を 1 からの差の群へ持ち上げる。
規約：KST Lemma 4.16 の M_{n,n} の作用、M の逆を使わない。
使われ方：μ、φ、ψ と帰納ホモトピーの外部同変性の接続。 -/
def triangularBlockMatrixEnd (n m : ℕ) (J : TwoSidedIdeal R) (M : Matrix (Fin n) (Fin n) R) :
    Monoid.End (triangularBlockGroup n m J) :=
  leftMultiplierGroupHom (blockPatternSubring (n + m) n J) (firstBlockMatrix n m M)
    (blockPattern_firstBlock_left_mem n m J M) (blockPattern_firstBlock_right_absorbed n m J M)

end SerrePositivity.KST.ProExcision
