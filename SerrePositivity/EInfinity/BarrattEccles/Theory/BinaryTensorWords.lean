module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.BigOperators

/-!
# 二色の入力語のテンソル

## 概要
HA 3.2.4.7 の自由代数の比較のため、二つの入力の和のテンソル冪を色付き語へ分ける。

## 方針
二色の語を再帰的に添字づけ、各語のテンソルの包含と射影を二項直和の射から作る。

## 規約
色の順序と、右に括った既存のテンソル冪を保つ。空の語はテンソル単位。

## 使われ方
色付き Schur 分解と、指定された自由代数の余積からテンソルへの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits MonoidalCategory MonoidalPreadditive
open SerrePositivity.TensorPowers
open scoped BigOperators

/-- 長さ n の二色の入力語。 -/
def BinaryTensorWord : ℕ → Type
  | 0 => PUnit
  | n + 1 => BinaryTensorWord n ⊕ BinaryTensorWord n

instance binaryTensorWordFintype : ∀ n, Fintype (BinaryTensorWord n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := binaryTensorWordFintype n
    exact inferInstanceAs (Fintype (BinaryTensorWord n ⊕ BinaryTensorWord n))

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (X Y : C) [HasBinaryBiproduct X Y]

/-- 入力語の色に従って並べたテンソル。 -/
def binaryTensorWordObj : ∀ n, BinaryTensorWord n → C
  | 0, _ => 𝟙_ C
  | n + 1, .inl w => X ⊗ binaryTensorWordObj n w
  | n + 1, .inr w => Y ⊗ binaryTensorWordObj n w

/-- 各入力語のテンソルから、和のテンソル冪への指定包含。 -/
def binaryTensorWordInclusion : ∀ n w, binaryTensorWordObj X Y n w ⟶ power (X ⊞ Y) n
  | 0, _ => 𝟙 _
  | n + 1, .inl w => biprod.inl ⊗ₘ binaryTensorWordInclusion n w
  | n + 1, .inr w => biprod.inr ⊗ₘ binaryTensorWordInclusion n w

/-- 和のテンソル冪から、指定した入力語のテンソルへの射影。 -/
def binaryTensorWordProjection : ∀ n w, power (X ⊞ Y) n ⟶ binaryTensorWordObj X Y n w
  | 0, _ => 𝟙 _
  | n + 1, .inl w => biprod.fst ⊗ₘ binaryTensorWordProjection n w
  | n + 1, .inr w => biprod.snd ⊗ₘ binaryTensorWordProjection n w

omit [MonoidalPreadditive C] in
/-- 同じ入力語の包含と射影の合成は恒等射。 -/
lemma binaryTensorWordInclusion_projection : ∀ n w,
    binaryTensorWordInclusion X Y n w ≫ binaryTensorWordProjection X Y n w = 𝟙 _ := by
  intro n
  induction n with
  | zero => intro w; exact Category.id_comp _
  | succ n ih =>
    intro w
    cases w with
    | inl w =>
      change (biprod.inl ⊗ₘ binaryTensorWordInclusion X Y n w) ≫
        (biprod.fst ⊗ₘ binaryTensorWordProjection X Y n w) = 𝟙 (X ⊗ _)
      rw [tensorHom_comp_tensorHom, biprod.inl_fst, ih]
      exact id_tensorHom_id _ _
    | inr w =>
      change (biprod.inr ⊗ₘ binaryTensorWordInclusion X Y n w) ≫
        (biprod.snd ⊗ₘ binaryTensorWordProjection X Y n w) = 𝟙 (Y ⊗ _)
      rw [tensorHom_comp_tensorHom, biprod.inr_snd, ih]
      exact id_tensorHom_id _ _

/-- 異なる入力語の包含と射影の合成は零射。 -/
lemma binaryTensorWordInclusion_projection_ne : ∀ n (w z : BinaryTensorWord n), w ≠ z →
    binaryTensorWordInclusion X Y n w ≫ binaryTensorWordProjection X Y n z = 0 := by
  intro n
  induction n with
  | zero => intro w z h; exact (h (show w = z from Subsingleton.elim (α := PUnit) _ _)).elim
  | succ n ih =>
    intro w z h
    cases w with
    | inl w =>
      cases z with
      | inl z =>
        change (_ ⊗ₘ binaryTensorWordInclusion X Y n w) ≫
          (_ ⊗ₘ binaryTensorWordProjection X Y n z) = _
        rw [tensorHom_comp_tensorHom, ih w z (fun e => h (congrArg Sum.inl e)), tensor_zero]
      | inr z =>
        change (biprod.inl ⊗ₘ _) ≫ (biprod.snd ⊗ₘ _) = _
        rw [tensorHom_comp_tensorHom, biprod.inl_snd, zero_tensor]
    | inr w =>
      cases z with
      | inl z =>
        change (biprod.inr ⊗ₘ _) ≫ (biprod.fst ⊗ₘ _) = _
        rw [tensorHom_comp_tensorHom, biprod.inr_fst, zero_tensor]
      | inr z =>
        change (_ ⊗ₘ binaryTensorWordInclusion X Y n w) ≫
          (_ ⊗ₘ binaryTensorWordProjection X Y n z) = _
        rw [tensorHom_comp_tensorHom, ih w z (fun e => h (congrArg Sum.inr e)), tensor_zero]

/-- 入力語の全ての射影と包含の合成の和は、元のテンソル冪の恒等射。 -/
lemma binaryTensorWord_total : ∀ n,
    (∑ w : BinaryTensorWord n,
      binaryTensorWordProjection X Y n w ≫ binaryTensorWordInclusion X Y n w) =
        𝟙 (power (X ⊞ Y) n) := by
  intro n
  induction n with
  | zero => simp [BinaryTensorWord, binaryTensorWordProjection, binaryTensorWordInclusion]
  | succ n ih =>
    change (∑ w : BinaryTensorWord n ⊕ BinaryTensorWord n,
      binaryTensorWordProjection X Y (n + 1) w ≫
        binaryTensorWordInclusion X Y (n + 1) w) = 𝟙 ((X ⊞ Y) ⊗ power (X ⊞ Y) n)
    rw [Fintype.sum_sum_type]
    simp only [binaryTensorWordProjection, binaryTensorWordInclusion, tensorHom_comp_tensorHom]
    rw [← tensor_sum, ← tensor_sum, ih, ← add_tensor, biprod.total]
    exact id_tensorHom_id _ _

end SerrePositivity.EInfinity
