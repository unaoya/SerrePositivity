module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPowerFirstCrossing
public import SerrePositivity.CategoryTheory.Monoidal.PermutationAction
public import SerrePositivity.GroupTheory.Coxeter.FirstToLast
public import SerrePositivity.GroupTheory.Coxeter.PermutationInduction

/-! # 先頭因子の移動と既存の対称群作用

有限置換の隣接互換による帰納で尾の作用を比較し、巡回置換の作用をbraidingへ接続する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.TensorPowers

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open SerrePositivity.Coxeter

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 尾の置換をずらした作用は、一因子を固定した左whisker。 -/
lemma permutationAction_shift (X : C) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permutationAction X (n + 1) (shiftPerm σ)).asIso.hom =
      X ◁ (permutationAction X n σ).asIso.hom := by
  cases n with
  | zero =>
    have hs : σ = 1 := Subsingleton.elim _ _
    subst σ
    rw [shiftPerm_one, permutationAction_one, permutationAction_one, whiskerLeft_id]
    rfl
  | succ n =>
    apply permutation_induction_right σ
    · rw [shiftPerm_one, permutationAction_one, permutationAction_one, whiskerLeft_id]
      rfl
    · intro τ i ih
      simp only [shiftPerm_mul, permutationAction_mul, shiftPerm_adjacent,
        permutationAction_adjacent, ih, whiskerLeft_comp]
      rfl

/-- 先頭を末尾へ送る置換の作用は、既存の隣接交換による同型。 -/
lemma permutationAction_firstToLast (X : C) (n : ℕ) :
    (permutationAction X (n + 1) (firstToLastPerm n)).asIso.hom = (moveFirstIso X n).hom := by
  induction n with
  | zero => exact permutationAction_one X 1
  | succ n ih =>
    rw [firstToLastPerm, permutationAction_mul, permutationAction_adjacent,
      permutationAction_shift, ih]
    rfl

/-- 逆向きの巡回置換の作用は、先頭因子をbraidingで末尾へ移して連結する射。 -/
lemma permutationAction_rotate_symm (X : C) (n : ℕ) :
    (permutationAction X (n + 1) (finRotate (n + 1)).symm).asIso.hom =
      (β_ X (power X n)).hom ≫ (power X n ◁ (ρ_ X).inv) ≫ (appendIso X n 1).hom := by
  rw [← firstToLastPerm_eq_rotate_symm, permutationAction_firstToLast, moveFirstIso_braiding]

/-- 順向きの巡回置換の作用は、先頭因子を末尾へ移す同型の逆射。 -/
lemma permutationAction_rotate (X : C) (n : ℕ) :
    (permutationAction X (n + 1) (finRotate (n + 1))).asIso.hom = (moveFirstIso X n).inv := by
  have h : (permutationAction X (n + 1) (finRotate (n + 1)).symm).asIso =
      moveFirstIso X n := by
    apply Iso.ext
    rw [← Coxeter.firstToLastPerm_eq_rotate_symm, permutationAction_firstToLast]
  have hh := congrArg Iso.inv h
  simpa only [← Equiv.Perm.inv_def, map_inv, Aut.inv_asIso, Iso.symm_inv] using hh
end SerrePositivity.TensorPowers
