module
public import SerrePositivity.KST.ProExcision.Claim415Factorization

/-!
# 列ベクトルの有限 rank のブロック包含

概要：列を零で埋めて大きい rank へ送る実加法準同型を構成する。
方針：first n の添字に元の列を入れ、残りを零にする。
規約：KST Claim 4.15 の通常の列の安定化。
使われ方：三角群を経る実因子化を通常の右乗法の写像と比較する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open scoped Matrix

/-- 概要：列ベクトルの末尾を零で埋める加法準同型。
方針：添字の値が n 未満の場合だけ元の列を評価する。
規約：KST Claim 4.15、有限 rank を n から n+m へ変える。
使われ方：標準の列の安定化。 -/
def columnBlockInclusion (A : Type u) [AddCommGroup A] (n m : ℕ) :
    (Fin n → A) →+ (Fin (n + m) → A) where
  toFun v i := if hi : i.val < n then v ⟨i.val, hi⟩ else 0
  map_zero' := by funext i; dsimp; split_ifs <;> rfl
  map_add' v w := by funext i; dsimp; split_ifs <;> simp only [add_zero]

/-- 概要：列のブロック包含の前半の成分。
方針：castAdd の値は元の添字の値。
規約：KST Claim 4.15。使われ方：元の列の保存。 -/
lemma columnBlockInclusion_left (A : Type u) [AddCommGroup A] (n m : ℕ)
    (v : Fin n → A) (i : Fin n) :
    columnBlockInclusion A n m v (Fin.castAdd m i) = v i := by
  simp [columnBlockInclusion]

/-- 概要：列のブロック包含の後半の成分は零。
方針：natAdd の値は n 以上。
規約：KST Claim 4.15。使われ方：追加した座標の零性。 -/
lemma columnBlockInclusion_right (A : Type u) [AddCommGroup A] (n m : ℕ)
    (v : Fin n → A) (i : Fin m) :
    columnBlockInclusion A n m v (Fin.natAdd n i) = 0 := by
  simp [columnBlockInclusion]

/-- 概要：列のブロック包含は単位ブロック和の左行列作用と可換。
方針：有限和を前半・後半に分け、四つのブロックを計算する。
規約：KST Claim 4.15、非可換な係数を保つ。
使われ方：通常の安定化による半直積射の同変性。 -/
lemma firstBlockMatrix_mul_columnInclusion {R : Type u} [Ring R]
    (n m : ℕ) (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    firstBlockMatrix n m M *ᵥ columnBlockInclusion R n m v =
      columnBlockInclusion R n m (M *ᵥ v) := by
  funext i
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i =>
    simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
    change (∑ j, firstBlockMatrix n m M (Fin.castAdd m i) j * columnBlockInclusion R n m v j) = _
    rw [Fin.sum_univ_add]
    simp only [firstBlockMatrix_left_left, firstBlockMatrix_left_right,
      columnBlockInclusion_left, columnBlockInclusion_right, mul_zero, Finset.sum_const_zero, add_zero]
    rfl
  | inr i =>
    simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right]
    change (∑ j, firstBlockMatrix n m M (Fin.natAdd n i) j * columnBlockInclusion R n m v j) = 0
    rw [Fin.sum_univ_add]
    simp only [firstBlockMatrix_right_left, firstBlockMatrix_right_right,
      columnBlockInclusion_left, columnBlockInclusion_right, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero]

end SerrePositivity.KST.ProExcision
