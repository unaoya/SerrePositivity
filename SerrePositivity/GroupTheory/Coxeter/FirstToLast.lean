module

public import SerrePositivity.GroupTheory.Coxeter.TypeA
public import Mathlib.GroupTheory.Perm.Fin

/-! # 先頭を末尾へ送る有限置換

先頭を固定する尾の置換と隣接互換の再帰で巡回置換を構成し、点での作用とMathlibの巡回置換を比較する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.Coxeter

/-- 先頭を固定し、尾の置換を一つ後ろへずらす。 -/
def shiftPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv n).symm.permCongr (Equiv.optionCongr σ)
/-- ずらした置換は先頭を固定する。 -/
@[simp] lemma shiftPerm_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : shiftPerm σ 0 = 0 := by
  simp [shiftPerm, Equiv.permCongr_def]
/-- 尾の位置では元の置換を一つずらして作用する。 -/
@[simp] lemma shiftPerm_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    shiftPerm σ i.succ = (σ i).succ := by
  simp [shiftPerm, Equiv.permCongr_def]
/-- 恒等置換をずらすと恒等置換。 -/
lemma shiftPerm_one (n : ℕ) : shiftPerm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
/-- 置換をずらす操作は乗法を保つ。 -/
lemma shiftPerm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    shiftPerm (σ * τ) = shiftPerm σ * shiftPerm τ := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [Equiv.Perm.mul_apply]
/-- 尾の隣接互換は一つ後ろの隣接互換へ送られる。 -/
lemma shiftPerm_adjacent (n : ℕ) (i : Fin n) :
    shiftPerm (adjacentTransposition i) = adjacentTransposition i.succ := by
  ext x
  refine Fin.cases ?_ (fun j ↦ ?_) x
  · have h₀ : (0 : Fin (n + 2)) ≠ i.castSucc.succ := (Fin.succ_ne_zero _).symm
    have h₁ : (0 : Fin (n + 2)) ≠ i.succ.succ := (Fin.succ_ne_zero _).symm
    simp [adjacentTransposition, Equiv.swap_apply_def, h₀, h₁]
  · simp [adjacentTransposition, Equiv.swap_apply_def]
    grind
/-- 隣接互換の列によって先頭を末尾へ送る置換。 -/
def firstToLastPerm : ∀ n, Equiv.Perm (Fin (n + 1))
  | 0 => 1
  | n + 1 => shiftPerm (firstToLastPerm n) * adjacentTransposition (0 : Fin (n + 1))
/-- 先頭の位置は末尾へ送られる。 -/
lemma firstToLastPerm_zero (n : ℕ) : firstToLastPerm n 0 = Fin.last n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [firstToLastPerm, Equiv.Perm.mul_apply, adjacentTransposition,
      Fin.castSucc_zero, Equiv.swap_apply_left, shiftPerm_succ, ih]
    rfl
/-- 先頭以外の位置は一つ前へ送られる。 -/
lemma firstToLastPerm_succ (n : ℕ) (i : Fin n) : firstToLastPerm n i.succ = i.castSucc := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [firstToLastPerm, Equiv.Perm.mul_apply, adjacentTransposition,
        Fin.castSucc_zero, Equiv.swap_apply_right, shiftPerm_zero]
    · have h₀ : j.succ.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero _
      have h₁ : j.succ.succ ≠ (0 : Fin (n + 1)).succ := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_zero] at hv
        omega
      simp only [firstToLastPerm, Equiv.Perm.mul_apply, adjacentTransposition]
      rw [Fin.castSucc_zero, Equiv.swap_apply_of_ne_of_ne h₀ h₁, shiftPerm_succ, ih]
      rfl

/-- 構成した置換はMathlibの逆向きの巡回置換。 -/
lemma firstToLastPerm_eq_rotate_symm (n : ℕ) : firstToLastPerm n = (finRotate (n + 1)).symm := by
  apply Equiv.ext
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [firstToLastPerm_zero]
    symm
    apply (finRotate (n + 1)).symm_apply_eq.mpr
    exact finRotate_last.symm
  · rw [firstToLastPerm_succ]
    symm
    apply (finRotate (n + 1)).symm_apply_eq.mpr
    exact (finRotate_of_lt j.isLt).symm

end SerrePositivity.Coxeter
