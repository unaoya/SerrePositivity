module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Group.End

/-! # 標準有限集合のブロック全単射

左右の有限全単射を、連結した標準有限集合上の全単射へまとめる。
スペクトルや添字圏に依存しない、有限集合についての一般論。
-/

@[expose] public section

namespace SerrePositivity.FiniteBijection

/-- 二つの全単射を、直和の二つのブロックに作用させる。 -/
def blockEquiv {m n m' n' : ℕ} (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n') :
    Fin (m + n) ≃ Fin (m' + n') :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr e f).trans finSumFinEquiv)

@[simp] lemma blockEquiv_refl (m n : ℕ) :
    blockEquiv (Equiv.refl (Fin m)) (Equiv.refl (Fin n)) = Equiv.refl (Fin (m + n)) := by
  ext x
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective x
  cases i <;> simp [blockEquiv]

lemma blockEquiv_trans {m n m' n' m'' n'' : ℕ}
    (e : Fin m ≃ Fin m') (f : Fin n ≃ Fin n')
    (e' : Fin m' ≃ Fin m'') (f' : Fin n' ≃ Fin n'') :
    (blockEquiv e f).trans (blockEquiv e' f') = blockEquiv (e.trans e') (f.trans f') := by
  ext x
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective x
  cases i <;> simp [blockEquiv]

/-- 左ブロックの二点の交換は、連結後の同じ二点の交換。 -/
lemma blockEquiv_swap_left (m n : ℕ) (i j : Fin m) :
    blockEquiv (Equiv.swap i j) (Equiv.refl (Fin n)) =
      Equiv.swap (i.castAdd n) (j.castAdd n) := by
  simp only [blockEquiv, Equiv.Perm.sumCongr_swap_refl]
  simpa only [← Equiv.trans_assoc, finSumFinEquiv_apply_left] using
    Equiv.symm_trans_swap_trans (Sum.inl i) (Sum.inl j) finSumFinEquiv
/-- 右ブロックの二点の交換は、左ブロックの長さだけずらした交換。 -/
lemma blockEquiv_swap_right (m n : ℕ) (i j : Fin n) :
    blockEquiv (Equiv.refl (Fin m)) (Equiv.swap i j) =
      Equiv.swap (i.natAdd m) (j.natAdd m) := by
  simp only [blockEquiv, Equiv.Perm.sumCongr_refl_swap]
  simpa only [← Equiv.trans_assoc, finSumFinEquiv_apply_right] using
    Equiv.symm_trans_swap_trans (Sum.inr i) (Sum.inr j) finSumFinEquiv

/-- ブロック全単射は左右の置換の乗法を保つ。 -/
lemma blockEquiv_mul {m n : ℕ} (σ τ : Equiv.Perm (Fin m))
    (α β : Equiv.Perm (Fin n)) :
    blockEquiv (σ * τ) (α * β) = blockEquiv σ α * blockEquiv τ β := by
  exact (blockEquiv_trans τ β σ α).symm

end SerrePositivity.FiniteBijection
