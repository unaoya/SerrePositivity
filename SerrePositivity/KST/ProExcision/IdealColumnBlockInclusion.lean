module
public import SerrePositivity.KST.ProExcision.LastColumnBlockInclusion

/-!
# イデアル内の列のブロック包含と行列作用

概要：係数イデアル内の零埋め列が単位ブロック和の行列作用と可換であることを証明する。
方針：前半・後半の成分と有限和のブロック分解を使う。
規約：KST Claim 4.15、右乗法と左行列作用の順を保つ。
使われ方：通常の有限 rank の半直積射の実構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：イデアル内の零埋め列を周囲環へ忘れると通常の零埋め列。
方針：各成分の所属証明を忘れ、二つの場合で定義を比較する。
規約：KST Claim 4.15。使われ方：実行列成分との同定。 -/
lemma columnBlockInclusion_coe (J : TwoSidedIdeal R) (n m : ℕ) (v : Fin n → J) :
    (fun i ↦ (columnBlockInclusion J n m v i : R)) =
      columnBlockInclusion R n m (fun i ↦ (v i : R)) := by
  funext i
  dsimp only [columnBlockInclusion, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> rfl

/-- 概要：イデアルの列のブロック包含は単位ブロック和の実作用に同変。
方針：二つの行ブロックで有限和を計算する。
規約：KST Claim 4.15、非可換な周囲環。
使われ方：基底のブロック和と列の零埋めが誘導する実半直積射。 -/
lemma idealColumnBlockInclusion_equivariant (J : TwoSidedIdeal R) (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    idealMatrixAction (n + m) J (firstBlockMatrix n m M)
        ((columnBlockInclusion J n m).toMultiplicative v) =
      (columnBlockInclusion J n m).toMultiplicative (idealMatrixAction n J M v) := by
  change idealMatrixVecHom (n + m) J (firstBlockMatrix n m M)
    (columnBlockInclusion J n m v.toAdd) = columnBlockInclusion J n m (idealMatrixVecHom n J M v.toAdd)
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i =>
    simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
    apply Subtype.ext
    change (∑ j, firstBlockMatrix n m M (Fin.castAdd m i) j *
      (columnBlockInclusion J n m v.toAdd j : R)) = ∑ j, M i j * (v.toAdd j : R)
    rw [Fin.sum_univ_add]
    simp only [firstBlockMatrix_left_left, firstBlockMatrix_left_right,
      columnBlockInclusion_left, columnBlockInclusion_right, zero_mul, Finset.sum_const_zero, add_zero]
  | inr i =>
    simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right]
    apply Subtype.ext
    change (∑ j, firstBlockMatrix n m M (Fin.natAdd n i) j *
      (columnBlockInclusion J n m v.toAdd j : R)) = 0
    rw [Fin.sum_univ_add]
    simp only [firstBlockMatrix_right_left, firstBlockMatrix_right_right,
      columnBlockInclusion_left, columnBlockInclusion_right, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero]
    simp

end SerrePositivity.KST.ProExcision
