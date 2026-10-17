module

public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# 任意の余モナドの反復冪に元の対象へのaugmentationを構成する

## 概要
任意の余モナドの反復冪に元の対象へのaugmentationを構成する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。

## 規約と注意
任意の圏と余モナドを入力し、モデル構造・局所可呈示性は要求しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はWaldhausenのS-構成の二重単体図式や分解の比較・加法性の準備に利用できる。
[棚卸し m0075][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0075
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All-degree face and degeneracy operators for an arbitrary comonad
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators
variable {C : Type u} [Category.{v} C] (G : Comonad C) (X : C)

def power : ℕ → C
  | 0 => X
  | n + 1 => G.obj (power n)

def face : (n : ℕ) → Fin (n + 1) → (power G X (n + 1) ⟶ power G X n)
  | 0, _ => G.ε.app X
  | n + 1, i => Fin.cases (G.ε.app (power G X (n + 1))) (fun j => G.map (face n j)) i

def degeneracy : (n : ℕ) → Fin (n + 1) → (power G X (n + 1) ⟶ power G X (n + 2))
  | 0, _ => G.δ.app X
  | n + 1, i => Fin.cases (G.δ.app (power G X (n + 1)))
      (fun j => G.map (degeneracy n j)) i

@[simp] lemma face_zero (n : ℕ) : face G X n 0 = G.ε.app (power G X n) := by
  cases n <;> rfl

@[simp] lemma face_succ (n : ℕ) (i : Fin (n + 1)) :
    face G X (n + 1) i.succ = G.map (face G X n i) := rfl

@[simp] lemma degeneracy_zero (n : ℕ) :
    degeneracy G X n 0 = G.δ.app (power G X n) := by cases n <;> rfl

@[simp] lemma degeneracy_succ (n : ℕ) (i : Fin (n + 1)) :
    degeneracy G X (n + 1) i.succ = G.map (degeneracy G X n i) := rfl

lemma face_face (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    face G X (n + 1) j.succ ≫ face G X n i =
      face G X (n + 1) i.castSucc ≫ face G X n j := by
  induction n with
  | zero =>
    fin_cases i
    fin_cases j
    exact G.ε.naturality (G.ε.app X)
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      simpa only [face_zero, face_succ, Fin.castSucc_zero, CategoryTheory.Functor.id_map] using
        G.ε.naturality (face G X (n + 1) j)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        have hij : i ≤ j := Fin.succ_le_succ_iff.mp h
        change G.map (face G X (n + 1) j.succ) ≫ G.map (face G X n i) =
          G.map (face G X (n + 1) i.castSucc) ≫ G.map (face G X n j)
        rw [← G.map_comp, ← G.map_comp, ih i j hij]

lemma degeneracy_face_self (n : ℕ) (i : Fin (n + 1)) :
    degeneracy G X n i ≫ face G X (n + 1) i.castSucc = 𝟙 _ := by
  induction n with
  | zero => fin_cases i; exact G.left_counit X
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact G.left_counit (power G X (n + 1))
    | succ i =>
      change G.map (degeneracy G X n i) ≫ G.map (face G X (n + 1) i.castSucc) = _
      rw [← G.map_comp, ih i, G.map_id]
      rfl

lemma degeneracy_face_succ (n : ℕ) (i : Fin (n + 1)) :
    degeneracy G X n i ≫ face G X (n + 1) i.succ = 𝟙 _ := by
  induction n with
  | zero => fin_cases i; exact G.right_counit X
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact G.right_counit (power G X (n + 1))
    | succ i =>
      change G.map (degeneracy G X n i) ≫ G.map (face G X (n + 1) i.succ) = _
      rw [← G.map_comp, ih i, G.map_id]
      rfl

lemma degeneracy_degeneracy (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    degeneracy G X n j ≫ degeneracy G X (n + 1) i.castSucc =
      degeneracy G X n i ≫ degeneracy G X (n + 1) j.succ := by
  induction n with
  | zero => fin_cases i; fin_cases j; exact (G.coassoc X).symm
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (G.coassoc (power G X (n + 1))).symm
      | succ j => exact G.δ.naturality (degeneracy G X n j)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        have hij : i ≤ j := Fin.succ_le_succ_iff.mp h
        change G.map (degeneracy G X n j) ≫ G.map (degeneracy G X (n + 1) i.castSucc) =
          G.map (degeneracy G X n i) ≫ G.map (degeneracy G X (n + 1) j.succ)
        rw [← G.map_comp, ← G.map_comp, ih i j hij]

lemma degeneracy_face_le (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : i ≤ j.castSucc) :
    degeneracy G X (n + 1) j.succ ≫ face G X (n + 2) i.castSucc =
      face G X (n + 1) i ≫ degeneracy G X n j := by
  induction n with
  | zero =>
    fin_cases i <;> fin_cases j
    · exact G.ε.naturality (G.δ.app X)
    · simp at h
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      simpa only [face_zero, degeneracy_succ, Fin.castSucc_zero,
        CategoryTheory.Functor.id_map] using G.ε.naturality (degeneracy G X (n + 1) j)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at h
      | succ j =>
        have hij : i ≤ j.castSucc := Fin.succ_le_succ_iff.mp h
        change G.map (degeneracy G X (n + 1) j.succ) ≫ G.map (face G X (n + 2) i.castSucc) =
          G.map (face G X (n + 1) i) ≫ G.map (degeneracy G X n j)
        rw [← G.map_comp, ← G.map_comp, ih i j hij]

lemma degeneracy_face_gt (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1))
    (h : j.castSucc < i) :
    degeneracy G X (n + 1) j.castSucc ≫ face G X (n + 2) i.succ =
      face G X (n + 1) i ≫ degeneracy G X n j := by
  induction n with
  | zero =>
    fin_cases i <;> fin_cases j
    · simp at h
    · exact (G.δ.naturality (G.ε.app X)).symm
  | succ n ih =>
    induction i using Fin.cases with
    | zero => simp at h
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (G.δ.naturality (face G X (n + 1) i)).symm
      | succ j =>
        have hij : j.castSucc < i := Fin.succ_lt_succ_iff.mp h
        change G.map (degeneracy G X (n + 1) j.castSucc) ≫ G.map (face G X (n + 2) i.succ) =
          G.map (face G X (n + 1) i) ≫ G.map (degeneracy G X n j)
        rw [← G.map_comp, ← G.map_comp, ih i j hij]

/-- 任意の余モナドの反復冪に元の対象へのaugmentationを構成する。

任意の圏と余モナドを入力し、モデル構造・局所可呈示性は要求しない。
余単位と余乗法、または自由な道の生成射を各次数で明示する。
面・退化の関係式と生成射上の一致から、全体の自然性と比較を導く。
-/
def augmentation : (n : ℕ) → (power G X n ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => G.ε.app (power G X n) ≫ augmentation n

lemma face_augmentation (n : ℕ) (i : Fin (n + 1)) :
    face G X n i ≫ augmentation G X n = augmentation G X (n + 1) := by
  induction n with
  | zero => fin_cases i; rfl
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      change G.map (face G X n i) ≫
        (G.ε.app (power G X n) ≫ augmentation G X n) = _
      rw [← Category.assoc, G.ε.naturality (face G X n i)]
      change (G.ε.app (power G X (n + 1)) ≫ face G X n i) ≫ augmentation G X n = _
      rw [Category.assoc, ih i]
      rfl

lemma degeneracy_augmentation (n : ℕ) (i : Fin (n + 1)) :
    degeneracy G X n i ≫ augmentation G X (n + 2) = augmentation G X (n + 1) := by
  rw [← face_augmentation G X (n + 1) i.castSucc, ← Category.assoc,
    degeneracy_face_self, Category.id_comp]

end SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators
