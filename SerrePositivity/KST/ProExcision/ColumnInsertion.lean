module
public import SerrePositivity.KST.ProExcision.IdealRightColumn

/-!
# 補助列と実座標挿入の整合

概要：恒等行・列の挿入は元の列行列を挿入後の列行列へ送る。
方針：指定点の零行・零列と、既存成分での succAbove の単射性を使う。
規約：KST Lemma 4.16 の φ の小さい帰納段階への因子化。
使われ方：帰納仮定の実群準同型の像と大きい群内の右乗法の同定。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]
variable {ι : Type v} [Fintype ι]

/-- 概要：補助列の全添字を挿入写像で移すと既存成分が保たれる。
方針：単一成分行列の有限和で succAbove の単射性を使う。
規約：KST 4.16。使われ方：実挿入の補助列上の公式。 -/
lemma blockColumn_succAbove {N : ℕ} (p : Fin (N + 1))
    (r : ι → Fin N) (q : Fin N) (v : ι → R) (i j : Fin N) :
    blockColumn (p.succAbove ∘ r) (p.succAbove q) v (p.succAbove i) (p.succAbove j) =
      blockColumn r q v i j := by
  simp only [blockColumn, Matrix.sum_apply, Matrix.single_apply, Function.comp_apply,
    Fin.succAbove_right_injective.eq_iff]

/-- 概要：挿入した補助行には移した列の非零成分がない。
方針：succAbove の像は指定点を含まない。
規約：KST 4.16。使われ方：実挿入の追加行での一致。 -/
lemma blockColumn_succAbove_row {N : ℕ} (p : Fin (N + 1))
    (r : ι → Fin N) (q : Fin N) (v : ι → R) (j : Fin (N + 1)) :
    blockColumn (p.succAbove ∘ r) (p.succAbove q) v p j = 0 := by
  simp [blockColumn, Matrix.sum_apply, Matrix.single_apply, Fin.succAbove_ne]

/-- 概要：挿入した補助列には移した列の非零成分がない。
方針：元の列 q の挿入像は指定点ではない。
規約：KST 4.16。使われ方：実挿入の追加列での一致。 -/
lemma blockColumn_succAbove_column {N : ℕ} (p : Fin (N + 1))
    (r : ι → Fin N) (q : Fin N) (v : ι → R) (i : Fin (N + 1)) :
    blockColumn (p.succAbove ∘ r) (p.succAbove q) v i p = 0 := by
  simp [blockColumn, Matrix.sum_apply, Matrix.single_apply, Fin.succAbove_ne]

/-- 概要：1+V の座標挿入は 1 と移した補助列の和。
方針：全添字を指定点と既存座標に分け、各成分の式で照合する。
規約：KST Lemma 4.16、非可換な実行列。
使われ方：小さい右乗法の帰納仮定と大きい群での φ の同定。 -/
lemma matrixInsertion_one_add_blockColumn {N : ℕ} (p : Fin (N + 1))
    (r : ι → Fin N) (q : Fin N) (v : ι → R) :
    matrixInsertionHom p (1 + blockColumn r q v) =
      1 + blockColumn (p.succAbove ∘ r) (p.succAbove q) v := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSuccEquiv' p).symm.surjective i
  obtain ⟨j, rfl⟩ := (finSuccEquiv' p).symm.surjective j
  cases i <;> cases j <;>
    simp [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some, Matrix.add_apply,
      matrixInsertion_self, matrixInsertion_row, matrixInsertion_column, matrixInsertion_succAbove,
      blockColumn_succAbove_row, blockColumn_succAbove_column, blockColumn_succAbove, Matrix.one_apply]

end SerrePositivity.KST.ProExcision
