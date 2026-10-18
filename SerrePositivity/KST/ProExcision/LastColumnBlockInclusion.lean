module
public import SerrePositivity.KST.ProExcision.ColumnBlockInclusion

/-!
# 実最終列から通常の列のブロック包含への同定

概要：最終列への実埋め込みを左上ブロックと通常の零埋め列で同定する。
方針：最後以外の列は零であり、行は前半・後半で評価する。
規約：KST Claim 4.15、非可換な実行列の成分計算。
使われ方：因子化による相対零化を通常の有限 rank 写像へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：最後の列だけを加えた行列の左上ブロックは恒等行列。
方針：残した列の添字は最後の列と異なるので単一成分行列の和が消える。
規約：KST Claim 4.15。使われ方：因子化の基底射は通常のブロック和。 -/
lemma matrixDropLast_one_add_lastColumn (n m : ℕ) (v : Fin n → R) :
    matrixDropLast (1 + blockColumn (Fin.castAdd (m + 1)) (Fin.last (n + m)) v) =
      (1 : Matrix (Fin (n + m)) (Fin (n + m)) R) := by
  apply Matrix.ext
  intro i j
  have hb : blockColumn (Fin.castAdd (m + 1)) (Fin.last (n + m)) v i.castSucc j.castSucc = 0 := by
    simp [blockColumn, Matrix.sum_apply, Matrix.single_apply, Ne.symm (Fin.castSucc_ne_last j)]
  change (1 : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) i.castSucc j.castSucc +
    blockColumn (Fin.castAdd (m + 1)) (Fin.last (n + m)) v i.castSucc j.castSucc = _
  rw [hb, add_zero]
  exact congrArg (fun A : Matrix (Fin (n + m)) (Fin (n + m)) R ↦ A i j) matrixDropLast_one

/-- 概要：最後の列だけを加えた行列の列成分は通常の零埋め列。
方針：前半の行では元のベクトル、後半の行では零になることを示す。
規約：KST Claim 4.15。使われ方：右乗法の列の実同定。 -/
lemma matrixLastColumn_one_add_lastColumn (n m : ℕ) (v : Fin n → R) :
    matrixLastColumn (1 + blockColumn (Fin.castAdd (m + 1)) (Fin.last (n + m)) v) =
      columnBlockInclusion R n m v := by
  funext i
  change (1 : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) R) i.castSucc (Fin.last (n + m)) +
    blockColumn (Fin.castAdd (m + 1)) (Fin.last (n + m)) v i.castSucc (Fin.last (n + m)) = _
  simp only [Matrix.one_apply, Fin.castSucc_ne_last, ite_false, zero_add]
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  cases i with
  | inl i =>
    simp only [finSumFinEquiv_apply_left, columnBlockInclusion_left]
    have he : (Fin.castAdd m i).castSucc = Fin.castAdd (m + 1) i := Fin.ext rfl
    rw [he, firstRows_blockColumn_apply, if_pos rfl]
  | inr i =>
    simp only [finSumFinEquiv_apply_right, columnBlockInclusion_right]
    have he : (Fin.natAdd n i).castSucc = Fin.natAdd n i.castSucc := Fin.ext rfl
    rw [he, otherRows_blockColumn_apply]

end SerrePositivity.KST.ProExcision
